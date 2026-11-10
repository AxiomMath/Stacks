module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Homology.ShortComplex.Homology
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.AugmentationContractible
public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.OrderedComplex
public import StacksFrontier.Topology.Sheaves.Modules.Exactness
public import StacksFrontier.Topology.Sheaves.Modules.StalkRestrictOpen
public import StacksFrontier.Algebra.Homology.StrictlyPerfectRestriction

/-!
# The extended alternating Čech complex of a ringed space, and its acyclicity off the equations

Let `(X, 𝒪)` be a ringed space — no scheme hypothesis anywhere in this file — let `F` be a
sheaf of `𝒪`-modules and let `U : I → Opens X` be a family of opens indexed by a linearly
ordered set. The *extended alternating Čech complex* of `F` for `U` is the complex of sheaves
of `𝒪`-modules whose degree-zero term is `F`, whose degree-`p+1` term is the sheaf
`V ↦ ∏_{i₀ < ⋯ < i_p} F(V ∩ U_{i₀} ∩ ⋯ ∩ U_{i_p})`, whose differential out of degree zero is
restriction and whose differentials in positive degrees are the signed alternating restriction
maps. This file constructs that complex and proves that it restricts to an acyclic complex
over `⨆ i, U i`.

Specialised to the opens `U i = X.basicOpen (f i)` attached to finitely many global functions
`f : Fin c → Γ(𝒪_X, ⊤)`, the union `⨆ i, X.basicOpen (f i)` is the complement of the common
zero locus `Z` of the `f i`, so this is Stacks 0G7K at ringed-space generality.

## Main definitions

* `Stacks.Cech.cechTerm`: the degree-`p+1` term, the sheaf of ordered Čech cochains.
* `Stacks.Cech.cechDiff` and `Stacks.Cech.cechAug`: the differentials and the augmentation.
* `Stacks.Cech.extendedCechComplex`: **the ringed-space form of Stacks 0G7J**, the complex
  itself.
* `Stacks.Cech.sectionsFunctor`: sections over an open, as a functor on sheaves of modules.

## Main results

* `Stacks.Cech.cechCochainPresheaf_isSheaf`: the presheaf of ordered Čech cochains of a sheaf
  is a sheaf — the input that makes the terms of the complex sheaves of modules.
* `Stacks.Cech.sectionComplexIso`: over an open `V` the complex of sections is the extended
  ordered Čech complex of the covering of `V` by the `V ⊓ U i`.
* `Stacks.Cech.sectionComplex_acyclic`: **the local statement.** If `V ≤ U i` for some `i`,
  that covering has `V` itself as a member, so Stacks 0G6T makes the complex of sections
  contractible, hence acyclic.
* `Stacks.Cech.extendedCechComplex_acyclic_restrict`: the complex restricted to `⨆ i, U i` is
  acyclic.
* `Stacks.Cech.extendedCechComplex_acyclic_restrict_basicOpen`: **Stacks 0G7K for an arbitrary
  ringed space**, the previous result for the principal opens of finitely many global
  functions. `Stacks.Cech.coe_iSup_basicOpen` identifies the open it is stated over with the
  complement of the common zero locus, and `Stacks.Cech.basicOpen_prod` identifies the Čech
  intersections with the opens `U_{i₀…i_p}` of Stacks 0G7I, the loci where the products
  `f_{i₀} ⋯ f_{i_p}` are invertible.

## Implementation notes

The degree-`p+1` term is built so that its sections over `V` are *literally*
`CechCochains.OrdCochain (fun i ↦ V ⊓ U i) F.val.presheaf p` and its differential is
*literally* `CechCochains.ordD`; this is what makes the comparison with the complex of
Tags 01FI/0G6T an isomorphism with identity components in positive degrees. Three things are
then owed. The `𝒪(V)`-module structure is the product of the module structures of the factors
with scalars restricted to the Čech intersections (`Stacks.Cech.cechCochainModule`). The sheaf
condition is obtained by exhibiting the cochain presheaf as a product of the summand presheaves
`V ↦ F(V ⊓ U_{i₀…i_p})`, each of which is a sheaf because it is the pushforward of `F` along
the continuous functor `V ↦ V ⊓ W` of `Stacks.Cech.interFunctor`; a product of sheaves is a
sheaf by `CategoryTheory.Sheaf.isSheaf_of_isLimit`. And `PresheafOfModules.ofPresheaf` turns
the resulting abelian sheaf, with those module structures, into a presheaf of modules without
changing it.

Acyclicity of the restriction is checked on stalks
(`AlgebraicGeometry.SheafOfModules.exact_iff_stalkShortComplex_exact`, Tag 01AG), and a point
of `⨆ i, U i` lies in some `U i`, which has arbitrarily small neighbourhoods of that point
inside it; `Stacks.Cech.stalkExact_of_sectionExact` upgrades exactness of the complexes of
sections over those neighbourhoods to exactness of the stalk complex, and
`Stacks.SheafOfModules.restrictStalkAddIso` compares the stalks of the restricted complex with
the stalks of the original one.

The index type is in `Type` — `Fin c` for the application — so that the Čech cochains live in
the same universe as the sections of `F`.

## References

* [Stacks Project, Tag 0G7K](https://stacks.math.columbia.edu/tag/0G7K)
* [Stacks Project, Tag 0G7I](https://stacks.math.columbia.edu/tag/0G7I)
* [Stacks Project, Tag 0G6T](https://stacks.math.columbia.edu/tag/0G6T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.Cech

variable {X : TopCat.{u}} {I : Type} [LinearOrder I]

/-! ### The functor `V ↦ V ⊓ W` and its continuity -/

/-- Intersecting with a fixed open, as a functor `Opens X ⥤ Opens X`. -/
def interFunctor (W : Opens X) : Opens X ⥤ Opens X :=
  Opens.map W.inclusion' ⋙ W.isOpenEmbedding.functor

/-- The functor `interFunctor W` sends `V` to `V ⊓ W`. -/
@[simp]
lemma interFunctor_obj (W V : Opens X) : (interFunctor W).obj V = V ⊓ W :=
  Opens.functor_map_eq_inf _ _

/-- Intersecting with a fixed open is continuous for the Grothendieck topology of opens. -/
instance interFunctor_isContinuous (W : Opens X) :
    (interFunctor W).IsContinuous (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology X) := by
  have := W.isOpenEmbedding.functor_isContinuous
  exact inferInstanceAs ((Opens.map W.inclusion' ⋙ W.isOpenEmbedding.functor).IsContinuous _ _)

/-! ### The presheaf of ordered Čech cochains -/

/-- Shrinking the ambient open shrinks every Čech intersection. -/
lemma inter_mono_of_le (U : I → Opens X) {V W : Opens X} (h : W ≤ V) {p : ℕ}
    (s : CechCochains.OrdIndex (I := I) p) :
    CechCochains.inter (fun i => W ⊓ U i) s.1 ≤
      CechCochains.inter (fun i => V ⊓ U i) s.1 :=
  iInf_mono fun _ => inf_le_inf_right _ h

/-- The presheaf of degree-`p` ordered Čech cochains of the family `fun i => V ⊓ U i`,
as `V` varies. -/
def cechCochainPresheaf (U : I → Opens X) (ℱ : TopCat.Presheaf AddCommGrpCat.{u} X) (p : ℕ) :
    (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj V := AddCommGrpCat.of (CechCochains.OrdCochain (fun i => V.unop ⊓ U i) ℱ p)
  map {V W} f := AddCommGrpCat.ofHom
    { toFun := fun x s => CechCochains.restr ℱ (inter_mono_of_le U (leOfHom f.unop) s) (x s)
      map_zero' := by funext s; exact map_zero _
      map_add' := fun x y => by funext s; exact map_add _ _ _ }
  map_id V := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    funext s
    change CechCochains.restr ℱ _ (x s) = x s
    simp only [CechCochains.restr]
    rw [show (homOfLE (inter_mono_of_le U (leOfHom (𝟙 V).unop) s)) = 𝟙 _ from
      Subsingleton.elim _ _]
    simp
  map_comp {V W Z} f g := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    funext s
    change CechCochains.restr ℱ _ (x s) =
      CechCochains.restr ℱ _ (CechCochains.restr ℱ _ (x s))
    rw [CechCochains.restr_restr]

/-- The restriction maps of the cochain presheaf restrict each component to the smaller Čech
intersection. -/
@[simp]
lemma cechCochainPresheaf_map_apply (U : I → Opens X)
    (ℱ : TopCat.Presheaf AddCommGrpCat.{u} X) {p : ℕ} {V W : (Opens X)ᵒᵖ} (f : V ⟶ W)
    (x : CechCochains.OrdCochain (fun i => V.unop ⊓ U i) ℱ p)
    (s : CechCochains.OrdIndex (I := I) p) :
    ((cechCochainPresheaf U ℱ p).map f) x s =
      CechCochains.restr ℱ (inter_mono_of_le U (leOfHom f.unop) s) (x s) := rfl

/-! ### The sheaf condition -/

/-- A Čech intersection of the shrunk family is the shrinking of the Čech intersection. -/
lemma inter_inf_eq (U : I → Opens X) {p : ℕ} (s : CechCochains.OrdIndex (I := I) p)
    (V : Opens X) :
    CechCochains.inter (fun i => V ⊓ U i) s.1 = V ⊓ CechCochains.inter U s.1 := by
  simp only [CechCochains.inter]
  exact (inf_iInf (f := fun k => U (s.1 k)) (a := V)).symm

/-- The presheaf `V ↦ ℱ(V ⊓ U_{i₀…i_p})`, one summand of the degree-`p` Čech cochains. -/
def cechComponentPresheaf (U : I → Opens X) (ℱ : TopCat.Presheaf AddCommGrpCat.{u} X) {p : ℕ}
    (s : CechCochains.OrdIndex (I := I) p) : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj V := ℱ.obj (op (CechCochains.inter (fun i => V.unop ⊓ U i) s.1))
  map {_ _} f := ℱ.map (homOfLE (inter_mono_of_le U (leOfHom f.unop) s)).op
  map_id V := by
    rw [show (homOfLE (inter_mono_of_le U (leOfHom (𝟙 V).unop) s)) = 𝟙 _ from
      Subsingleton.elim _ _]
    simp
  map_comp {_ _ _} _ _ := by rw [← ℱ.map_comp, ← op_comp]; congr 1

/-- The summand presheaf is the pushforward of `ℱ` along `V ↦ V ⊓ U_{i₀…i_p}`. -/
def cechComponentIso (U : I → Opens X) (ℱ : TopCat.Presheaf AddCommGrpCat.{u} X) {p : ℕ}
    (s : CechCochains.OrdIndex (I := I) p) :
    cechComponentPresheaf U ℱ s ≅
      (interFunctor (CechCochains.inter U s.1)).op ⋙ ℱ :=
  NatIso.ofComponents
    (fun V => ℱ.mapIso (eqToIso (congrArg op
      (by rw [interFunctor_obj, inter_inf_eq] : CechCochains.inter (fun i => V.unop ⊓ U i) s.1 =
        (interFunctor (CechCochains.inter U s.1)).obj V.unop))))
    (fun {V W} _ => by
      dsimp [cechComponentPresheaf]
      rw [← ℱ.map_comp, ← ℱ.map_comp]
      exact congrArg ℱ.map (Subsingleton.elim _ _))

/-- The summand presheaf of a sheaf is a sheaf. -/
lemma cechComponentPresheaf_isSheaf (U : I → Opens X)
    (ℱ : TopCat.Presheaf AddCommGrpCat.{u} X)
    (hℱ : CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology X) ℱ) {p : ℕ}
    (s : CechCochains.OrdIndex (I := I) p) :
    CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology X)
      (cechComponentPresheaf U ℱ s) :=
  (CategoryTheory.Presheaf.isSheaf_of_iso_iff (cechComponentIso U ℱ s)).2
    (Functor.op_comp_isSheaf _ _ _ ⟨ℱ, hℱ⟩)

variable (U : I → Opens X) (ℱ : TopCat.Presheaf AddCommGrpCat.{u} X)
  (hℱ : CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology X) ℱ)

/-- The summands of the degree-`p` Čech cochains, as a diagram of sheaves. -/
def cechComponentDiagram (p : ℕ) :
    Discrete (CechCochains.OrdIndex (I := I) p) ⥤
      Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  Discrete.functor fun s => ⟨cechComponentPresheaf U ℱ s, cechComponentPresheaf_isSheaf U ℱ hℱ s⟩

/-- The cochain presheaf, with its projections, as a cone over the summands. -/
def cechCochainCone (p : ℕ) :
    Cone (cechComponentDiagram U ℱ hℱ p ⋙
      sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) where
  pt := cechCochainPresheaf U ℱ p
  π :=
    { app := fun s =>
        { app := fun _ => AddCommGrpCat.ofHom
            { toFun := fun x => x s.as
              map_zero' := rfl
              map_add' := fun _ _ => rfl }
          naturality := fun _ _ _ => rfl }
      naturality := by
        rintro ⟨s⟩ ⟨t⟩ ⟨⟨rfl⟩⟩
        simp }

/-- The cone of projections is a limit cone: a cochain is exactly a family of sections. -/
def cechCochainConeIsLimit (p : ℕ) : IsLimit (cechCochainCone U ℱ hℱ p) :=
  evaluationJointlyReflectsLimits _ fun V =>
    { lift := fun S => AddCommGrpCat.ofHom
        { toFun := fun y t => (S.π.app ⟨t⟩).hom y
          map_zero' := by funext t; exact map_zero _
          map_add' := fun _ _ => by funext t; exact map_add _ _ _ }
      fac := fun _ _ => by ext; rfl
      uniq := fun _ _ hm => by
        ext y
        funext t
        exact ConcreteCategory.congr_hom (hm ⟨t⟩) y }

include hℱ in
/-- **The presheaf of ordered Čech cochains of a sheaf is a sheaf.** -/
lemma cechCochainPresheaf_isSheaf (p : ℕ) :
    CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology X)
      (cechCochainPresheaf U ℱ p) :=
  CategoryTheory.Sheaf.isSheaf_of_isLimit _ _ (cechCochainConeIsLimit U ℱ hℱ p)

/-! ### The Čech cochains as a presheaf of modules -/

section Term

variable {O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}

/-- A Čech intersection lies inside the ambient open. -/
lemma cechInter_le (U : I → Opens X) {p : ℕ} (s : CechCochains.OrdIndex (I := I) p)
    (V : Opens X) : CechCochains.inter (fun i => V ⊓ U i) s.1 ≤ V :=
  le_trans (iInf_le _ (0 : Fin (p + 1))) inf_le_left

/-- Restriction of scalars from the ambient open to a Čech intersection. -/
def cechScalarRes (U : I → Opens X) (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    {p : ℕ} (s : CechCochains.OrdIndex (I := I) p) (V : (Opens X)ᵒᵖ) :
    O.obj.obj V ⟶ O.obj.obj (op (CechCochains.inter (fun i => V.unop ⊓ U i) s.1)) :=
  O.obj.map (homOfLE (cechInter_le U s V.unop)).op

/-- The `𝒪(V)`-module structure on degree-`p` Čech cochains over `V`: a scalar acts on each
component after restriction to the corresponding Čech intersection. -/
instance cechCochainModule (U : I → Opens X) (F : SheafOfModules.{u} O) (p : ℕ)
    (V : (Opens X)ᵒᵖ) :
    Module (O.obj.obj V) ((cechCochainPresheaf U F.val.presheaf p).obj V) :=
  letI : ∀ s : CechCochains.OrdIndex (I := I) p,
      Module (O.obj.obj V)
        (F.val.presheaf.obj (op (CechCochains.inter (fun i => V.unop ⊓ U i) s.1))) :=
    fun s => Module.compHom _ (cechScalarRes U O s V).hom
  Pi.module _ _ _

/-- A scalar acts on each component of a cochain through its restriction to the corresponding
Čech intersection. -/
lemma cechCochainModule_smul_apply (U : I → Opens X) (F : SheafOfModules.{u} O) (p : ℕ)
    (V : (Opens X)ᵒᵖ) (r : O.obj.obj V)
    (x : (cechCochainPresheaf U F.val.presheaf p).obj V)
    (s : CechCochains.OrdIndex (I := I) p) :
    (r • x) s = (cechScalarRes U O s V).hom r • x s := rfl

/-- Restricting a scalar to the ambient open and then to a Čech intersection is restricting
it to the Čech intersection directly. -/
lemma cechScalarRes_naturality (U : I → Opens X)
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) {p : ℕ}
    (s : CechCochains.OrdIndex (I := I) p) {V W : (Opens X)ᵒᵖ} (f : V ⟶ W) :
    cechScalarRes U O s V ≫
        O.obj.map (homOfLE (inter_mono_of_le U (leOfHom f.unop) s)).op =
      O.obj.map f ≫ cechScalarRes U O s W := by
  simp only [cechScalarRes, ← O.obj.map_comp]
  exact congrArg O.obj.map (Subsingleton.elim _ _)

/-- `Stacks.Cech.cechScalarRes_naturality`, evaluated at a scalar. -/
lemma cechScalarRes_naturality_apply (U : I → Opens X)
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) {p : ℕ}
    (s : CechCochains.OrdIndex (I := I) p) {V W : (Opens X)ᵒᵖ} (f : V ⟶ W)
    (r : O.obj.obj V) :
    (O.obj.map (homOfLE (inter_mono_of_le U (leOfHom f.unop) s)).op).hom
        ((cechScalarRes U O s V).hom r) =
      (cechScalarRes U O s W).hom ((O.obj.map f).hom r) :=
  congrArg (fun φ : O.obj.obj V ⟶ _ => φ.hom r) (cechScalarRes_naturality U O s f)

/-- **The extended alternating Čech complex of Stacks 0G7J, term by term**: the presheaf of
modules of degree-`p` ordered Čech cochains for the family `fun i ↦ V ⊓ U i`. -/
def cechTermVal (U : I → Opens X) (F : SheafOfModules.{u} O) (p : ℕ) :
    PresheafOfModules.{u} O.obj :=
  PresheafOfModules.ofPresheaf (cechCochainPresheaf U F.val.presheaf p) (by
    intro V W f r m
    funext s
    change (F.val.map (homOfLE (inter_mono_of_le U (leOfHom f.unop) s)).op)
        ((cechScalarRes U O s V).hom r • m s) =
      (cechScalarRes U O s W).hom ((O.obj.map f).hom r) •
        (F.val.map (homOfLE (inter_mono_of_le U (leOfHom f.unop) s)).op) (m s)
    exact (PresheafOfModules.map_smul F.val _ _ _).trans
      (congrArg (fun z => z •
          (F.val.map (homOfLE (inter_mono_of_le U (leOfHom f.unop) s)).op) (m s))
        (cechScalarRes_naturality_apply U O s f r)))

/-- The underlying presheaf of abelian groups of `cechTermVal U F p` is the cochain presheaf. -/
@[simp]
lemma cechTermVal_presheaf (U : I → Opens X) (F : SheafOfModules.{u} O) (p : ℕ) :
    (cechTermVal U F p).presheaf = cechCochainPresheaf U F.val.presheaf p := rfl

/-- **Stacks 0G7J, term by term**, as a sheaf of modules. -/
def cechTerm (U : I → Opens X) (F : SheafOfModules.{u} O) (p : ℕ) :
    SheafOfModules.{u} O where
  val := cechTermVal U F p
  isSheaf := cechCochainPresheaf_isSheaf U F.val.presheaf F.isSheaf p

/-- The sections of `cechTerm U F p` over `V` are the degree-`p` ordered Čech cochains of the
family `fun i ↦ V ⊓ U i`. -/
@[simp]
lemma cechTerm_obj (U : I → Opens X) (F : SheafOfModules.{u} O) (p : ℕ)
    (V : (Opens X)ᵒᵖ) :
    ((cechTerm U F p).val.obj V : Type u) =
      CechCochains.OrdCochain (fun i => V.unop ⊓ U i) F.val.presheaf p := rfl

/-! ### The differential and the augmentation -/

/-- Restriction is semilinear for the Čech scalar restrictions. -/
lemma restr_cechScalarRes_smul (U : I → Opens X) (F : SheafOfModules.{u} O) {p q : ℕ}
    (s : CechCochains.OrdIndex (I := I) p) (t : CechCochains.OrdIndex (I := I) q)
    (V : (Opens X)ᵒᵖ)
    (h : CechCochains.inter (fun i => V.unop ⊓ U i) t.1 ≤
      CechCochains.inter (fun i => V.unop ⊓ U i) s.1)
    (r : O.obj.obj V)
    (y : F.val.presheaf.obj (op (CechCochains.inter (fun i => V.unop ⊓ U i) s.1))) :
    CechCochains.restr F.val.presheaf h ((cechScalarRes U O s V).hom r • y) =
      (cechScalarRes U O t V).hom r • CechCochains.restr F.val.presheaf h y :=
  (PresheafOfModules.map_smul F.val _ _ _).trans
    (congrArg (fun z => z • CechCochains.restr F.val.presheaf h y)
      (congrArg (fun φ : O.obj.obj V ⟶ _ => φ.hom r)
        (show cechScalarRes U O s V ≫ O.obj.map (homOfLE h).op = cechScalarRes U O t V from by
          simp only [cechScalarRes, ← O.obj.map_comp]
          exact congrArg O.obj.map (Subsingleton.elim _ _))))

/-- The alternating sum of the two-step restrictions of a section of `ℱ` over `V` to a degree-one
Čech intersection vanishes. -/
private theorem sum_restr_cechInter_le_eq_zero (U : I → Opens X)
    (ℱ : TopCat.Presheaf AddCommGrpCat.{u} X) (V : Opens X) (x : ℱ.obj (op V))
    (t : CechCochains.OrdIndex (I := I) 1) :
    ∑ j : Fin 2, ((-1 : ℤ) ^ (j : ℕ)) •
      CechCochains.restr ℱ (CechCochains.inter_le_omit (fun i => V ⊓ U i) t.1 j)
        (CechCochains.restr ℱ
          (cechInter_le U ⟨t.1 ∘ j.succAbove, CechCochains.strictMono_omit t.2 j⟩ V) x) = 0 := by
  simp only [CechCochains.restr_restr, Fin.sum_univ_two, Fin.isValue, Fin.val_zero, pow_zero,
    one_smul, Fin.val_one, pow_one, neg_smul, add_neg_cancel]

/-- The ordered Čech differential, as a morphism of presheaves of abelian groups. -/
def cechDiffPresheaf (U : I → Opens X) (ℱ : TopCat.Presheaf AddCommGrpCat.{u} X) (p : ℕ) :
    cechCochainPresheaf U ℱ p ⟶ cechCochainPresheaf U ℱ (p + 1) where
  app V := AddCommGrpCat.ofHom (CechCochains.ordD (fun i => V.unop ⊓ U i) ℱ p)
  naturality {V W} f := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    funext t
    change ∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
        CechCochains.restr ℱ (CechCochains.inter_le_omit (fun i => W.unop ⊓ U i) t.1 j)
          (CechCochains.restr ℱ (inter_mono_of_le U (leOfHom f.unop)
            ⟨t.1 ∘ j.succAbove, CechCochains.strictMono_omit t.2 j⟩)
            (x ⟨t.1 ∘ j.succAbove, CechCochains.strictMono_omit t.2 j⟩)) =
      CechCochains.restr ℱ (inter_mono_of_le U (leOfHom f.unop) t)
        (∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
          CechCochains.restr ℱ (CechCochains.inter_le_omit (fun i => V.unop ⊓ U i) t.1 j)
            (x ⟨t.1 ∘ j.succAbove, CechCochains.strictMono_omit t.2 j⟩))
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, CechCochains.restr_restr, CechCochains.restr_restr]

/-- **The differential of the extended alternating Čech complex of Stacks 0G7J**: the signed
alternating restriction map, as a morphism of sheaves of modules. -/
def cechDiff (U : I → Opens X) (F : SheafOfModules.{u} O) (p : ℕ) :
    cechTerm U F p ⟶ cechTerm U F (p + 1) where
  val := PresheafOfModules.homMk (cechDiffPresheaf U F.val.presheaf p) (by
    intro V r m
    funext t
    change ∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
        CechCochains.restr F.val.presheaf
            (CechCochains.inter_le_omit (fun i => V.unop ⊓ U i) t.1 j)
          ((cechScalarRes U O ⟨t.1 ∘ j.succAbove,
              CechCochains.strictMono_omit t.2 j⟩ V).hom r •
            m ⟨t.1 ∘ j.succAbove, CechCochains.strictMono_omit t.2 j⟩) =
      (cechScalarRes U O t V).hom r •
        ∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
          CechCochains.restr F.val.presheaf
            (CechCochains.inter_le_omit (fun i => V.unop ⊓ U i) t.1 j)
            (m ⟨t.1 ∘ j.succAbove, CechCochains.strictMono_omit t.2 j⟩)
    refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) Finset.smul_sum.symm
    exact (congrArg (fun z => ((-1 : ℤ) ^ (j : ℕ)) • z)
        (restr_cechScalarRes_smul U F
          ⟨t.1 ∘ j.succAbove, CechCochains.strictMono_omit t.2 j⟩ t V
          (CechCochains.inter_le_omit (fun i => V.unop ⊓ U i) t.1 j) r
          (m ⟨t.1 ∘ j.succAbove, CechCochains.strictMono_omit t.2 j⟩))).trans
      (smul_comm _ _ _))

/-- The augmentation `F ⟶ Č⁰`, restriction of a section to each member of the family. -/
def cechAugPresheaf (U : I → Opens X) (ℱ : TopCat.Presheaf AddCommGrpCat.{u} X) :
    ℱ ⟶ cechCochainPresheaf U ℱ 0 where
  app V := AddCommGrpCat.ofHom
    { toFun := fun y s => CechCochains.restr ℱ (cechInter_le U s V.unop) y
      map_zero' := by funext s; exact map_zero _
      map_add' := fun _ _ => by funext s; exact map_add _ _ _ }
  naturality {V W} f := by
    ext y
    funext s
    change CechCochains.restr ℱ (cechInter_le U s W.unop)
        (CechCochains.restr ℱ (leOfHom f.unop) y) =
      CechCochains.restr ℱ (inter_mono_of_le U (leOfHom f.unop) s)
        (CechCochains.restr ℱ (cechInter_le U s V.unop) y)
    rw [CechCochains.restr_restr, CechCochains.restr_restr]

/-- **The augmentation of the extended alternating Čech complex of Stacks 0G7J**, as a
morphism of sheaves of modules. -/
def cechAug (U : I → Opens X) (F : SheafOfModules.{u} O) : F ⟶ cechTerm U F 0 where
  val := PresheafOfModules.homMk (cechAugPresheaf U F.val.presheaf) (by
    intro V r y
    funext s
    exact PresheafOfModules.map_smul F.val _ _ _)

/-! ### The complex -/

/-- Two consecutive Čech differentials compose to zero. -/
lemma cechDiff_comp_cechDiff (U : I → Opens X) (F : SheafOfModules.{u} O) (p : ℕ) :
    cechDiff U F p ≫ cechDiff U F (p + 1) = 0 := by
  ext V x
  exact CechCochains.ordD_ordD (fun i => V.unop ⊓ U i) F.val.presheaf p x

/-- The augmentation composed with the first Čech differential is zero. -/
lemma cechAug_comp_cechDiff (U : I → Opens X) (F : SheafOfModules.{u} O) :
    cechAug U F ≫ cechDiff U F 0 = 0 := by
  ext V x
  funext t
  exact sum_restr_cechInter_le_eq_zero U F.val.presheaf V.unop x t

/-- The positive-degree part of the extended alternating Čech complex. -/
def extendedCechComplexAux (U : I → Opens X) (F : SheafOfModules.{u} O) :
    CochainComplex (SheafOfModules.{u} O) ℕ :=
  CochainComplex.of (fun p => cechTerm U F p) (fun p => cechDiff U F p)
    (cechDiff_comp_cechDiff U F)

/-- The differential of `extendedCechComplexAux U F` from degree `p` is `cechDiff U F p`. -/
@[simp]
lemma extendedCechComplexAux_d (U : I → Opens X) (F : SheafOfModules.{u} O) (p : ℕ) :
    (extendedCechComplexAux U F).d p (p + 1) = cechDiff U F p :=
  CochainComplex.of_d _ _ _

/-- **Stacks 0G7J for an arbitrary ringed space**: the extended alternating Čech complex of a
sheaf of modules `F` and a family of opens `U`. Its degree-zero term is `F`, its degree-`p+1`
term is the sheaf of ordered Čech cochains, its differential out of degree zero is the
restriction map and in positive degrees the signed alternating restriction map. -/
@[ega "0 12.1.4" "The sheaf complex C^•(U"]
def extendedCechComplex (U : I → Opens X) (F : SheafOfModules.{u} O) :
    CochainComplex (SheafOfModules.{u} O) ℕ :=
  (extendedCechComplexAux U F).augment (cechAug U F) (by
    rw [extendedCechComplexAux_d]
    exact cechAug_comp_cechDiff U F)

/-- The degree-zero term of the extended alternating Čech complex is `F`. -/
@[simp]
lemma extendedCechComplex_X_zero (U : I → Opens X) (F : SheafOfModules.{u} O) :
    (extendedCechComplex U F).X 0 = F := rfl

/-- The degree-`p+1` term of the extended alternating Čech complex is `cechTerm U F p`. -/
@[simp]
lemma extendedCechComplex_X_succ (U : I → Opens X) (F : SheafOfModules.{u} O) (p : ℕ) :
    (extendedCechComplex U F).X (p + 1) = cechTerm U F p := rfl

/-- The differential out of degree zero of the extended alternating Čech complex is the
augmentation. -/
@[simp]
lemma extendedCechComplex_d_zero_one (U : I → Opens X) (F : SheafOfModules.{u} O) :
    (extendedCechComplex U F).d 0 1 = cechAug U F := rfl

/-- The differential out of degree `p+1` of the extended alternating Čech complex is
`cechDiff U F p`. -/
@[simp]
lemma extendedCechComplex_d_succ (U : I → Opens X) (F : SheafOfModules.{u} O) (p : ℕ) :
    (extendedCechComplex U F).d (p + 1) (p + 1 + 1) = cechDiff U F p :=
  extendedCechComplexAux_d U F p

/-! ### Sections of the complex -/

/-- Sections over an open, as a functor on sheaves of modules. -/
def sectionsFunctor (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (V : Opens X) :
    SheafOfModules.{u} O ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.forget O ⋙ PresheafOfModules.toPresheaf O.obj ⋙
    (evaluation ((Opens X)ᵒᵖ) AddCommGrpCat.{u}).obj (op V)

/-- Taking sections over an open preserves zero morphisms. -/
instance sectionsFunctor_preservesZeroMorphisms
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (V : Opens X) :
    (sectionsFunctor O V).PreservesZeroMorphisms := by
  constructor
  intro A B
  rfl

/-- The augmentation of the ordered Čech complex of the family `fun i ↦ V ⊓ U i` composes to
zero with the first differential. -/
lemma orderedCechAugmentation_comp_d (U : I → Opens X)
    (ℱ : TopCat.Presheaf AddCommGrpCat.{u} X) (V : Opens X) :
    orderedCechAugmentation X ℱ (fun i => V ⊓ U i) (fun _ => inf_le_left) ≫
        (orderedCechComplex (fun i => V ⊓ U i) ℱ).d 0 1 = 0 := by
  rw [orderedCechComplex_d]
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro y
  funext t
  exact sum_restr_cechInter_le_eq_zero U ℱ V y.down t

/-- The extended ordered Čech complex of the family `fun i ↦ V ⊓ U i`, in abelian groups. -/
def orderedAugmented (U : I → Opens X) (ℱ : TopCat.Presheaf AddCommGrpCat.{u} X)
    (V : Opens X) : CochainComplex AddCommGrpCat.{u} ℕ :=
  (orderedCechComplex (fun i => V ⊓ U i) ℱ).augment
    (orderedCechAugmentation X ℱ (fun i => V ⊓ U i) (fun _ => inf_le_left))
    (orderedCechAugmentation_comp_d U ℱ V)

/-- The differential out of degree zero of `orderedAugmented U ℱ V` is the augmentation. -/
@[simp]
lemma orderedAugmented_d_zero_one (U : I → Opens X)
    (ℱ : TopCat.Presheaf AddCommGrpCat.{u} X) (V : Opens X) :
    (orderedAugmented U ℱ V).d 0 1 =
      orderedCechAugmentation X ℱ (fun i => V ⊓ U i) (fun _ => inf_le_left) := rfl

/-- The differential out of degree `p+1` of `orderedAugmented U ℱ V` is the ordered Čech
differential. -/
@[simp]
lemma orderedAugmented_d_succ (U : I → Opens X)
    (ℱ : TopCat.Presheaf AddCommGrpCat.{u} X) (V : Opens X) (p : ℕ) :
    (orderedAugmented U ℱ V).d (p + 1) (p + 1 + 1) =
      AddCommGrpCat.ofHom (CechCochains.ordD (fun i => V ⊓ U i) ℱ p) :=
  orderedCechComplex_d _ _ p

/-- The additive equivalence between an abelian group and its lift `ULift.{0} A`. -/
def upAddEquiv {A : Type u} [AddCommGroup A] : A ≃+ ULift.{0} A where
  toFun := ULift.up
  invFun := ULift.down
  left_inv _ := rfl
  right_inv x := by cases x; rfl
  map_add' _ _ := rfl

/-- **The sections of the extended alternating Čech complex over an open `V` form the extended
ordered Čech complex of the covering of `V` by the `V ⊓ U i`.** -/
def sectionComplexIso (U : I → Opens X) (F : SheafOfModules.{u} O) (V : Opens X) :
    (((sectionsFunctor O V).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (extendedCechComplex U F)) ≅ orderedAugmented U F.val.presheaf V := by
  let K := ((sectionsFunctor O V).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (extendedCechComplex U F)
  let T := orderedAugmented U F.val.presheaf V
  let e0 : K.X 0 ≅ T.X 0 := AddEquiv.ulift.symm.toAddCommGrpIso
  let es : ∀ p : ℕ, K.X (p + 1) ≅ T.X (p + 1) := fun _ => Iso.refl _
  refine HomologicalComplex.Hom.isoOfComponents
    (fun n => match n with
      | 0 => e0
      | p + 1 => es p) ?_
  intro p q hpq
  have hq : q = p + 1 := (show p + 1 = q by simpa [ComplexShape.up_Rel] using hpq).symm
  subst hq
  cases p with
  | zero =>
      dsimp only [K, T, es, e0, Functor.mapHomologicalComplex_obj_d]
      rw [extendedCechComplex_d_zero_one, orderedAugmented_d_zero_one]
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro y
      funext s
      rfl
  | succ p =>
      dsimp only [K, T, es, Functor.mapHomologicalComplex_obj_d]
      rw [extendedCechComplex_d_succ, orderedAugmented_d_succ]
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro y
      funext t
      rfl

/-- **Stacks 0G7K, the local statement**: over an open contained in one of the `U i` the
extended alternating Čech complex has contractible, hence acyclic, complex of sections. -/
lemma sectionComplex_acyclic (U : I → Opens X) (F : SheafOfModules.{u} O) (V : Opens X)
    (i : I) (hV : V ≤ U i) :
    (((sectionsFunctor O V).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (extendedCechComplex U F)).Acyclic := by
  have hcontract := orderedCechComplex_augment_homotopyEquiv_zero_of_eq X F.val.presheaf
    (fun j => V ⊓ U j) (fun _ => inf_le_left) i (inf_eq_left.mpr hV)
  have h : HomotopyEquiv (orderedAugmented U F.val.presheaf V)
      (HomologicalComplex.zero : CochainComplex AddCommGrpCat.{u} ℕ) :=
    Classical.choice hcontract.choose_spec
  have h' := (HomotopyEquiv.ofIso (sectionComplexIso U F V)).trans h
  rw [HomologicalComplex.acyclic_iff]
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  have hz : Limits.IsZero
      ((HomologicalComplex.zero : CochainComplex AddCommGrpCat.{u} ℕ).homology n) :=
    ShortComplex.isZero_homology_of_isZero_X₂
      ((HomologicalComplex.zero : CochainComplex AddCommGrpCat.{u} ℕ).sc n)
      (Limits.isZero_zero AddCommGrpCat.{u})
  exact Limits.IsZero.of_iso hz (h'.toHomologyIso n)

/-! ### From sections to stalks -/

/-- If a complex of sheaves of modules has exact complex of sections over every small enough
open neighbourhood of `x`, then its stalk complex at `x` is exact. -/
lemma stalkExact_of_sectionExact (K : CochainComplex (SheafOfModules.{u} O) ℕ) (x : X)
    (W : Opens X) (hxW : x ∈ W)
    (hsec : ∀ V : Opens X, V ≤ W → x ∈ V → ∀ n : ℕ,
      (((sectionsFunctor O V).mapHomologicalComplex (ComplexShape.up ℕ)).obj K).ExactAt n)
    (n : ℕ) :
    (AlgebraicGeometry.SheafOfModules.stalkShortComplex O (K.sc n) x).Exact := by
  let S := K.sc n
  let P₁ : TopCat.Presheaf AddCommGrpCat.{u} X := S.X₁.val.presheaf
  let P₂ : TopCat.Presheaf AddCommGrpCat.{u} X := S.X₂.val.presheaf
  let P₃ : TopCat.Presheaf AddCommGrpCat.{u} X := S.X₃.val.presheaf
  rw [ShortComplex.ab_exact_iff]
  intro z hz
  obtain ⟨V, hxV, s, hs⟩ := P₂.exists_germ_eq z
  have hgz : P₃.germ V x hxV (S.g.val.app (op V) s) = 0 :=
    (TopCat.Presheaf.stalkFunctor_map_germ_apply V x hxV
        ((PresheafOfModules.toPresheaf O.obj).map S.g.val) s).symm.trans
      (show ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          ((PresheafOfModules.toPresheaf O.obj).map S.g.val))
          (P₂.germ V x hxV s) = 0 by rwa [hs])
  obtain ⟨W₀, hxW₀, iW₀V, iV, hs0⟩ := P₃.germ_eq x hxV hxV
    (S.g.val.app (op V) s) 0 (by simpa using hgz)
  let A := W₀ ⊓ W
  have hxA : x ∈ A := ⟨hxW₀, hxW⟩
  let iAW₀ : A ⟶ W₀ := homOfLE inf_le_left
  let iAV : A ⟶ V := iAW₀ ≫ iW₀V
  let L := ((sectionsFunctor O A).mapHomologicalComplex (ComplexShape.up ℕ)).obj K
  have hFunc : Function.Exact (L.sc n).f (L.sc n).g :=
    (ShortComplex.ab_exact_iff_function_exact _).mp (hsec A inf_le_right hxA n)
  let sA := P₂.map iAV.op s
  have hs0A : P₃.map iAV.op (S.g.val.app (op V) s) = 0 := by
    have hsplit : P₃.map iAV.op = P₃.map iW₀V.op ≫ P₃.map iAW₀.op := by
      rw [← P₃.map_comp, ← op_comp]
    rw [hsplit]
    change P₃.map iAW₀.op (P₃.map iW₀V.op (S.g.val.app (op V) s)) = 0
    rw [hs0]
    simp
  have hsA : (L.sc n).g sA = 0 :=
    (PresheafOfModules.naturality_apply S.g.val iAV.op s).trans hs0A
  obtain ⟨tA, htA⟩ := Set.mem_range.mp ((hFunc sA).mp hsA)
  let tA' : P₁.obj (op A) := tA
  have htA'' : (S.f.val.app (op A)) tA' = sA := htA
  refine ⟨P₁.germ A x hxA tA', ?_⟩
  refine Eq.trans (TopCat.Presheaf.stalkFunctor_map_germ_apply A x hxA
    ((PresheafOfModules.toPresheaf O.obj).map S.f.val) tA') ?_
  change P₂.germ A x hxA ((S.f.val.app (op A)) tA') = z
  rw [htA'']
  exact (P₂.germ_res_apply iAV x hxA s).trans hs

/-! ### Acyclicity over the union of the family -/

/-- The stalk complex of the restriction to an open is the stalk complex of the original
complex at the corresponding point. -/
def restrictStalkShortComplexIso (W : Opens X) (O : Sheaf (Opens.grothendieckTopology X)
      RingCat.{u}) (y : (Opens.toTopCat X).obj W)
    (S : ShortComplex (SheafOfModules.{u} O)) :
    AlgebraicGeometry.SheafOfModules.stalkShortComplex
        (Stacks.SheafOfModules.restrictSheafOfRings W.isOpenEmbedding O)
        (S.map (Stacks.SheafOfModules.restrictSheafOfModules.{u} W.isOpenEmbedding O)) y ≅
      AlgebraicGeometry.SheafOfModules.stalkShortComplex O S (W.inclusion' y) :=
  ShortComplex.isoMk
    (Stacks.SheafOfModules.restrictStalkAddIso W.isOpenEmbedding O y S.X₁)
    (Stacks.SheafOfModules.restrictStalkAddIso W.isOpenEmbedding O y S.X₂)
    (Stacks.SheafOfModules.restrictStalkAddIso W.isOpenEmbedding O y S.X₃)
    (by
      ext m
      exact (Stacks.SheafOfModules.restrictStalkAddIso_hom_stalkMap
        W.isOpenEmbedding O y S.f m).symm)
    (by
      ext m
      exact (Stacks.SheafOfModules.restrictStalkAddIso_hom_stalkMap
        W.isOpenEmbedding O y S.g m).symm)

/-- **Stacks 0G7K for an arbitrary family of opens on an arbitrary ringed space**: the
extended alternating Čech complex of `U` restricts to an acyclic complex over `⨆ i, U i`. -/
theorem extendedCechComplex_acyclic_restrict (U : I → Opens X) (F : SheafOfModules.{u} O) :
    (((Stacks.SheafOfModules.restrictSheafOfModules.{u}
          (⨆ i, U i).isOpenEmbedding O).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (extendedCechComplex U F)).Acyclic := by
  rw [HomologicalComplex.acyclic_iff]
  intro n
  apply (AlgebraicGeometry.SheafOfModules.exact_iff_stalkShortComplex_exact
    (Stacks.SheafOfModules.restrictSheafOfRings (⨆ i, U i).isOpenEmbedding O) _).2
  intro y
  obtain ⟨i, hyi⟩ := Opens.mem_iSup.mp y.2
  have hOrig : (AlgebraicGeometry.SheafOfModules.stalkShortComplex O
      ((extendedCechComplex U F).sc n) ((⨆ i, U i).inclusion' y)).Exact := by
    refine stalkExact_of_sectionExact (extendedCechComplex U F) _ (U i) hyi ?_ n
    intro V hV _ m
    have hac := sectionComplex_acyclic U F V i hV
    rw [HomologicalComplex.acyclic_iff] at hac
    exact hac m
  exact (ShortComplex.exact_iff_of_iso
    (restrictStalkShortComplexIso (⨆ i, U i) O y ((extendedCechComplex U F).sc n))).2 hOrig

end Term

/-! ### The ringed-space form of Stacks 0G7K -/

section RingedSpace

open AlgebraicGeometry StrictlyPerfect

variable (Y : AlgebraicGeometry.RingedSpace.{u, u}) {c : ℕ}
  (g : Fin c → Y.presheaf.obj (op ⊤))

/-- The complement of the common zero locus of finitely many global functions is the union of
the opens on which they are invertible. -/
lemma coe_iSup_basicOpen (Y : AlgebraicGeometry.RingedSpace.{u, u}) {c : ℕ}
    (g : Fin c → Y.presheaf.obj (op ⊤)) :
    ((⨆ i, Y.basicOpen (g i) : Opens Y.carrier) : Set Y.carrier) =
      (Y.zeroLocus (Set.range g))ᶜ := by
  simp only [AlgebraicGeometry.RingedSpace.zeroLocus, Set.biInter_range, Set.compl_iInter,
    compl_compl, Opens.coe_iSup]

/-- The locus on which a finite product of global functions is invertible is the intersection
of the loci on which they are invertible: the opens `U_{i₀…i_p}` of Stacks 0G7I are the Čech
intersections used here. -/
lemma basicOpen_prod (Y : AlgebraicGeometry.RingedSpace.{u, u}) {n : ℕ}
    (h : Fin n → Y.presheaf.obj (op ⊤)) :
    Y.basicOpen (∏ k, h k) = ⨅ k, Y.basicOpen (h k) := by
  induction n with
  | zero =>
      simp only [Finset.univ_eq_empty, Finset.prod_empty, iInf_of_empty]
      exact AlgebraicGeometry.RingedSpace.basicOpen_of_isUnit Y isUnit_one
  | succ n ih =>
      rw [Fin.prod_univ_succ, AlgebraicGeometry.RingedSpace.basicOpen_mul,
        ih (fun k => h k.succ)]
      refine le_antisymm (le_iInf fun k => ?_)
        (le_inf (iInf_le _ 0) (le_iInf fun j => iInf_le _ j.succ))
      exact Fin.cases inf_le_left (fun j => inf_le_right.trans (iInf_le _ j)) k

/-- **Stacks 0G7K for an arbitrary ringed space.** Let `Y` be a ringed space, let
`g 0, …, g (c-1)` be global sections of its structure sheaf, let `Z` be their common zero
locus and let `F` be a sheaf of `𝒪_Y`-modules. Then the extended alternating Čech complex of
`F` for the opens `Y.basicOpen (g i)` restricts to an acyclic complex over `Y ∖ Z`, which is
the open `⨆ i, Y.basicOpen (g i)` by `Stacks.Cech.coe_iSup_basicOpen`.

The proof is `Stacks.Cech.sectionComplex_acyclic`: over an open contained in one of the
`Y.basicOpen (g i)` the complex of sections is the extended ordered Čech complex of a covering
one of whose members is the whole open, hence is contractible by Stacks 0G6T; exactness of a
complex of sheaves of modules is checked on stalks, and every point of `Y ∖ Z` has arbitrarily
small neighbourhoods inside some `Y.basicOpen (g i)`. -/
@[stacks 0G7K]
theorem extendedCechComplex_acyclic_restrict_basicOpen
    (F : OXMod.{u, u} Y) :
    (((restrictModules.{u, u, u} Y (⨆ i, Y.basicOpen (g i))).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj
      (extendedCechComplex (fun i => Y.basicOpen (g i)) F)).Acyclic :=
  extendedCechComplex_acyclic_restrict (fun i => Y.basicOpen (g i)) F

end RingedSpace

end Stacks.Cech
