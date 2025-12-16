theory Restrictive_Comp
  imports CryptHOL.CryptHOL
begin

text \<open>We introduce the notion of restrictive computational models. 
These are models in which the adversary is restricted, in the sense that 
it's output follows certain rules that can be enforced by constraints composed 
of the input to and the output of the adversary.

We formalize this notion in 3 components: 
1. the restrictive_comp_sel record -- purpose: select relevant elements from the input
2. the restrictive_comp_con record -- purpose: constrain output elements to the list 
of relevant (selected) elements.
3. restrict locale -- purpose: select relevant elements from the input and enforce constrains 
on the output.
TODO describe architecture in more detail\<close>

subsection \<open>restrictive_comp_sel\<close>

text \<open>A record to select the relevant elements from a type (data structure).
The naming-convention to support automation is *your_type*S, e.g. for int: intS\<close>
record ('a,'b) restrictive_comp_sel = select::"'a \<Rightarrow>'b list" (\<open>\<currency>\<index>\<close>)

text \<open>We provide a few generalized (data) structures that extend any definition for a 
restrictive_comp_sel.\<close>

context
  fixes r :: "('a,'b) restrictive_comp_sel"
begin

definition listS::
  "('a list, 'b) restrictive_comp_sel"
  where "listS \<equiv> \<lparr>select = (\<lambda>xs. concat (map (\<lambda>x. \<currency>\<^bsub>r\<^esub>x) xs))\<rparr>"

definition treeS :: 
  "('a tree, 'b) restrictive_comp_sel"
  where "treeS \<equiv> \<lparr>select = (\<lambda>x. \<currency>\<^bsub>listS\<^esub>(inorder x))\<rparr>"

end

context
  fixes r :: "('a::linorder,'b) restrictive_comp_sel"
begin

definition multisetS :: 
  "('a multiset, 'b) restrictive_comp_sel"
  where "multisetS \<equiv> \<lparr>select = (\<lambda>x. \<currency>\<^bsub>listS r\<^esub> (sorted_list_of_multiset x))\<rparr>"


definition fsetS :: 
  "('a fset, 'b) restrictive_comp_sel"
  where "fsetS \<equiv> \<lparr>select = (\<lambda>x. \<currency>\<^bsub>listS r\<^esub> (sorted_list_of_fset x))\<rparr>" 

end

context
  fixes ra :: "('a,'c) restrictive_comp_sel"
  and rb :: "('b,'c) restrictive_comp_sel"
begin

definition prodS::
  "(('a \<times> 'b), 'c) restrictive_comp_sel" where
  "prodS \<equiv> \<lparr>select = (\<lambda>(a,b). \<currency>\<^bsub>ra\<^esub>a @ \<currency>\<^bsub>rb\<^esub>b)\<rparr>"

end

context
  fixes ra :: "('a::linorder,'c) restrictive_comp_sel"
  and rb :: "('b,'c) restrictive_comp_sel"
begin

definition fmapS::
  "(('a, 'b) fmap, 'c) restrictive_comp_sel" where
  "fmapS \<equiv> \<lparr>select = (\<lambda>fm. \<currency>\<^bsub>listS (prodS ra rb)\<^esub> (sorted_list_of_fmap fm))\<rparr>"

end

subsection \<open>restrictive_comp_con\<close>

text \<open>A record to constrain an (output) element given a list of (input) values. 
constrain returns a Boolean value that states whether the constraint holds.
The naming-convention to support automation is *your_type*C, e.g. for int: intC\<close>
record ('a,'b) restrictive_comp_con = constrain::"'b list \<Rightarrow> 'a \<Rightarrow> bool"(infixl \<open>\<Znrres>\<index>\<close> 70)

text \<open>We provide a few generalized (data) structures that extend any definition for a 
restrictive_comp.\<close>

context
  fixes r :: "('a,'b) restrictive_comp_con"
begin

definition listC::
  "('a list, 'b) restrictive_comp_con"
  where "listC \<equiv> \<lparr>constrain = (\<lambda>ip op. list_all (\<lambda>x. ip \<Znrres>\<^bsub>r\<^esub> x) op)\<rparr>"

definition treeC :: 
  "('a tree, 'b) restrictive_comp_con"
  where "treeC \<equiv> \<lparr>constrain = (\<lambda>ip op. ip \<Znrres>\<^bsub>listC\<^esub>(inorder op))\<rparr>"

end

context
  fixes r :: "('a::linorder,'b) restrictive_comp_con"
begin

definition multisetC :: 
  "('a multiset, 'b) restrictive_comp_con"
  where "multisetC \<equiv> \<lparr>constrain = (\<lambda>ip op. ip \<Znrres>\<^bsub>listC r\<^esub> (sorted_list_of_multiset op))\<rparr>"


definition fsetC :: 
  "('a fset, 'b) restrictive_comp_con"
  where "fsetC \<equiv> \<lparr>constrain = (\<lambda>ip op. ip \<Znrres>\<^bsub>listC r\<^esub> (sorted_list_of_fset op))\<rparr>" 

end

context
  fixes ra :: "('a,'c) restrictive_comp_con"
  and rb :: "('b,'c) restrictive_comp_con"
begin

definition prodC::
  "(('a \<times> 'b), 'c) restrictive_comp_con" where
  "prodC \<equiv> \<lparr>constrain = (\<lambda>ip (opa,opb). ip \<Znrres>\<^bsub>ra\<^esub> opa \<and> ip \<Znrres>\<^bsub>rb\<^esub> opb)\<rparr>"

end

context
  fixes ra :: "('a::linorder,'c) restrictive_comp_con"
  and rb :: "('b,'c) restrictive_comp_con"
begin

definition fmapC::
  "(('a, 'b) fmap, 'c) restrictive_comp_con" where
  "fmapC \<equiv> \<lparr>constrain = (\<lambda>ip op. ip \<Znrres>\<^bsub>listC (prodC ra rb)\<^esub> (sorted_list_of_fmap op))\<rparr>"

end

subsection \<open>restrict\<close>

locale restrictive_comp = 
  fixes sel :: "('a,'b) restrictive_comp_sel"
  and con :: "('c,'b) restrictive_comp_con"
begin

text \<open>Given an adversary _restrict_ itself becomes a _restricted_ adversary that returns 
the given adversaries if and only if they meet the constraints, otherwise it fails.
The constraints are primarily characterized by the constrain function in con (select in sel is 
essentially pre-processing).\<close>
definition restrict :: "('a \<Rightarrow> 'c spmf) \<Rightarrow> 'a \<Rightarrow> 'c spmf" where 
  "restrict \<A> arg \<equiv> do {
  res \<leftarrow> \<A> arg;
  _::unit \<leftarrow> assert_spmf ((\<currency>\<^bsub>sel\<^esub> arg) \<Znrres>\<^bsub>con\<^esub> res);
  return_spmf res
  }"

end


subsection \<open>Examples\<close>

locale examples 
begin 

text \<open>examples for select\<close>

definition intS :: "(int,int) restrictive_comp_sel"
  where "intS \<equiv> \<lparr>select = (\<lambda>x. [x])\<rparr>"

lemma "\<currency>\<^bsub>intS\<^esub> (1::int) = [1::int]"
  unfolding intS_def
  by simp

lemma "(select (listS (listS intS))) [[1]] = [1]"
  apply(simp add: listS_def intS_def)
  done

lemma "\<currency>\<^bsub>listS (listS intS)\<^esub> [[1]] = [1]"
  unfolding listS_def intS_def
  by fastforce

lemma "\<currency>\<^bsub>prodS (listS intS) intS\<^esub> ([1],0) = [1,0]"
  unfolding prodS_def listS_def intS_def
  by fastforce

text \<open>examples for constrain\<close>

definition intC :: "(int, int) restrictive_comp_con"
  where "intC \<equiv> \<lparr>constrain = (\<lambda>ip op. sum_list ip = op)\<rparr>"

lemma "[0,1,2] \<Znrres>\<^bsub>intC\<^esub> 3"
  unfolding intC_def 
  by simp

lemma "[0,1,2] \<Znrres>\<^bsub>listC intC\<^esub> [3,3,3]"
  unfolding listC_def intC_def
  by simp

lemma "[0,1,2] \<Znrres>\<^bsub>prodC (listC intC) intC\<^esub> ([3,3,3],3)"
  unfolding listC_def intC_def prodC_def
  by fastforce

end

end