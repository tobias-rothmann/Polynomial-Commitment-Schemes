theory Restrictive_Comp
  imports CryptHOL.CryptHOL
begin

text \<open>We formalize the notion of restrictive computational models. 
These are models in which the adversary is restricted, in the sense that 
it's output follows certain rules that can be enforced by constraints composed 
of the input to and the output of the adversary.

We formalize this notion in 3 components: 
1. the Select record -- purpose: select relevant elements from the input
2. the Constrain record -- purpose: constrain output elements to the list 
of relevant (selected) seen elements.
3. Restrictive_Comp locale -- purpose: select relevant elements from the input and enforce constrains 
on the output.

This model is an abstraction over computational models like the Algebraic Group Model (AGM), 
the Algebraic Group Action Model (AGAM), the Algebraic Isogeny Model (AIM), and variants thereof.

We implement generalizations for model-type specific implementations to standard type constructors 
in Isabelle, including (e.g. group) lists, trees, multisets, finite sets, products, and finite maps. 
E.g. a model specific implementation of a group type can be generalized to a group list 
implementation.
Additionally, we provide default implementations noSelect and noConstrain, which select no element
and define no constraints on all inputs.
\<close>

subsection \<open>Select\<close>

text \<open>A record to select the relevant elements from a type (data structure).
The naming-convention to support automation is *your_type*S, e.g. for int: intS\<close>
record ('a,'b) Select = select::"'a \<Rightarrow>'b list" (\<open>\<currency>\<index>\<close>)

text \<open>We provide a few generalized type constructor implementations.\<close>

context
  fixes r :: "('a,'b) Select"
begin

definition listS::
  "('a list, 'b) Select"
  where "listS \<equiv> \<lparr>select = (\<lambda>xs. concat (map (\<lambda>x. \<currency>\<^bsub>r\<^esub>x) xs))\<rparr>"

definition treeS :: 
  "('a tree, 'b) Select"
  where "treeS \<equiv> \<lparr>select = (\<lambda>x. \<currency>\<^bsub>listS\<^esub>(inorder x))\<rparr>"

end

context
  fixes r :: "('a::linorder,'b) Select"
begin

definition multisetS :: 
  "('a multiset, 'b) Select"
  where "multisetS \<equiv> \<lparr>select = (\<lambda>x. \<currency>\<^bsub>listS r\<^esub> (sorted_list_of_multiset x))\<rparr>"


definition fsetS :: 
  "('a fset, 'b) Select"
  where "fsetS \<equiv> \<lparr>select = (\<lambda>x. \<currency>\<^bsub>listS r\<^esub> (sorted_list_of_fset x))\<rparr>" 

end

context
  fixes ra :: "('a,'c) Select"
  and rb :: "('b,'c) Select"
begin

definition prodS::
  "(('a \<times> 'b), 'c) Select" where
  "prodS \<equiv> \<lparr>select = (\<lambda>(a,b). \<currency>\<^bsub>ra\<^esub>a @ \<currency>\<^bsub>rb\<^esub>b)\<rparr>"

end

context
  fixes ra :: "('a::linorder,'c) Select"
  and rb :: "('b,'c) Select"
begin

definition fmapS::
  "(('a, 'b) fmap, 'c) Select" where
  "fmapS \<equiv> \<lparr>select = (\<lambda>fm. \<currency>\<^bsub>listS (prodS ra rb)\<^esub> (sorted_list_of_fmap fm))\<rparr>"

end

definition noSelect :: "('a, 'b) Select"
  where "noSelect \<equiv> \<lparr>select = (\<lambda>x. [])\<rparr>"

lemma noSelectEmpty[simp]: "\<And>x. \<currency>\<^bsub>noSelect\<^esub>x = []"
  by (simp add: noSelect_def)

subsection \<open>restrictive_comp_con\<close>

text \<open>A record to constrain an (output) element given a list of (input) values. 
constrain returns a Boolean value that states whether the constraint holds.
The naming-convention to support automation is *your_type*C, e.g. for int: intC\<close>
record ('b,'c) Constrain = constrain::"'b list \<Rightarrow> 'c \<Rightarrow> bool"(infixl \<open>\<Znrres>\<index>\<close> 70)

text \<open>We provide a few generalized (data) structures that extend any definition for a 
restrictive_comp.\<close>

context
  fixes r :: "('b,'c) Constrain"
begin

definition listC::
  "('b, 'c list) Constrain"
  where "listC \<equiv> \<lparr>constrain = (\<lambda>ip op. list_all (\<lambda>x. ip \<Znrres>\<^bsub>r\<^esub> x) op)\<rparr>"

definition treeC :: 
  "('b, 'c tree) Constrain"
  where "treeC \<equiv> \<lparr>constrain = (\<lambda>ip op. ip \<Znrres>\<^bsub>listC\<^esub>(inorder op))\<rparr>"

end

context
  fixes r :: "('b,'c::linorder) Constrain"
begin

definition multisetC :: 
  "('b, 'c multiset) Constrain"
  where "multisetC \<equiv> \<lparr>constrain = (\<lambda>ip op. ip \<Znrres>\<^bsub>listC r\<^esub> (sorted_list_of_multiset op))\<rparr>"


definition fsetC :: 
  "('b, 'c fset) Constrain"
  where "fsetC \<equiv> \<lparr>constrain = (\<lambda>ip op. ip \<Znrres>\<^bsub>listC r\<^esub> (sorted_list_of_fset op))\<rparr>" 

end

context
  fixes ra :: "('b,'c) Constrain"
  and rb :: "('b,'d) Constrain"
begin

definition prodC::
  "('b, 'c \<times> 'd) Constrain" where
  "prodC \<equiv> \<lparr>constrain = (\<lambda>ip (opa,opb). ip \<Znrres>\<^bsub>ra\<^esub> opa \<and> ip \<Znrres>\<^bsub>rb\<^esub> opb)\<rparr>"

end

context
  fixes ra :: "('b,'c::linorder) Constrain"
  and rb :: "('b,'d) Constrain"
begin

definition fmapC::
  "('b, ('c,'d) fmap) Constrain" where
  "fmapC \<equiv> \<lparr>constrain = (\<lambda>ip op. ip \<Znrres>\<^bsub>listC (prodC ra rb)\<^esub> (sorted_list_of_fmap op))\<rparr>"

end

definition noConstrain :: "('b,'c) Constrain"
  where "noConstrain \<equiv>  \<lparr>constrain = (\<lambda>ip op. True)\<rparr>"

lemma noConstrainTrue[simp]: "\<And>ip op. ip \<Znrres>\<^bsub>noConstrain\<^esub> op = True"
  by (simp add: noConstrain_def)

subsection \<open>restrict\<close>

locale Restrictive_Comp = 
  fixes sel :: "('a,'b) Select"
  and con :: "('b,'c) Constrain"
begin

text \<open>Applied to an adversary _restrict_ itself becomes a _restricted_ adversary that returns 
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

definition intS :: "(int,int) Select"
  where "intS \<equiv> \<lparr>select = (\<lambda>x. [x])\<rparr>"

lemma "\<currency>\<^bsub>intS\<^esub> (1::int) = [1::int]"
  unfolding intS_def
  by simp

lemma "\<currency>\<^bsub>listS intS\<^esub> [1] = [1]"
  by(simp add: listS_def intS_def)

lemma "\<currency>\<^bsub>listS (listS intS)\<^esub> [[1]] = [1]"
  unfolding listS_def intS_def
  by fastforce

lemma "\<currency>\<^bsub>prodS (listS intS) intS\<^esub> ([1],0) = [1,0]"
  unfolding prodS_def listS_def intS_def
  by fastforce

text \<open>examples for constrain\<close>

definition intC :: "(int, int) Constrain"
  where "intC \<equiv> \<lparr>constrain = (\<lambda>ip op. sum_list ip = op)\<rparr>"

lemma "[0,1,2] \<Znrres>\<^bsub>intC\<^esub> 3"
  by (simp add: intC_def)

lemma "[0,1,2] \<Znrres>\<^bsub>listC intC\<^esub> [3,3,3]"
  unfolding listC_def intC_def
  by simp

lemma "[0,1,2] \<Znrres>\<^bsub>prodC (listC intC) intC\<^esub> ([3,3,3],3)"
  unfolding listC_def intC_def prodC_def
  by fastforce

end

end