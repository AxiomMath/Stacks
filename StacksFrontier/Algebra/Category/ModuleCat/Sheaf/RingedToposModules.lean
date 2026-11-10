module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforward
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedTopos
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.ChangeOfRingsAdjunction
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# Pullback and pushforward of sheaves of modules on ringed topoi

Let `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi: a morphism of
topoi `f` together with a map of structure sheaves. Stacks 03D6 defines the pushforward of a
sheaf of `O_C`-modules `F` as the direct image `f_*F` with its scalar action restricted along
`f♯ : O_D ⟶ f_*O_C`, and the pullback of a sheaf of `O_D`-modules `G` as
`O_C ⊗_{f⁻¹O_D} f⁻¹G`. Stacks 03D7 is the assertion that these are adjoint:
`Hom_{O_C}(f^*G, F) = Hom_{O_D}(G, f_*F)`.

The proof is the one in the source: the adjunction is the composite of the change-of-rings
adjunction of Stacks 03CZ on `Sh(C)` along `f⁻¹O_D ⟶ O_C` with the inverse-image/direct-image
adjunction of Stacks 03D3 for the morphism of topoi `f`, the latter being proved here for an
arbitrary morphism of topoi.

## Main definitions

* `Stacks.Sheaves.RingedToposModules.ofSheafHom`, `homEquivSubtype`: a morphism of sheaves of
  modules is the same thing as a morphism of the underlying sheaves of sets which is additive
  and compatible with scalar multiplication.
* `Stacks.Sheaves.RingedToposModules.inverseImageModules`,
  `directImageModules`: the inverse image of sheaves of modules along a morphism of topoi
  (Stacks 03D2) and the direct image over the inverse-image ring, read as a sheaf of
  `O`-modules by restriction of scalars along the unit `O ⟶ f_*f⁻¹O`.
* `Stacks.Sheaves.RingedToposModules.inverseImageModuleSheafIso`: the inverse image of a sheaf
  of modules and the inverse image of its underlying sheaf of sets are the same sheaf of sets,
  as an isomorphism of functors.
* `Stacks.Sheaves.RingedToposModules.commRingSheaf`, `extendScalars`: extension of scalars
  for sheaves of modules along a morphism of sheaves of commutative rings on a site.
* `Stacks.Sheaves.RingedToposModules.inverseImageCommRingPresheaf`: the inverse image of a
  sheaf of commutative rings along a morphism of topoi, as a presheaf of commutative rings.
* `Stacks.Sheaves.RingedToposModules.RingedToposHom`: a morphism of ringed topoi.
* `Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules`,
  `Stacks.Sheaves.RingedToposModules.pushforwardModules`: the two functors of Stacks 03D6.

## Main results

* `Stacks.Sheaves.RingedToposModules.homEquiv_binary_iff`: a square expressing compatibility
  of a morphism `Φ A ⟶ B` with a binary operation holds if and only if the corresponding
  square for its adjunct holds. This is the mechanism by which linearity is transported
  across the adjunction `f⁻¹ ⊣ f_*`.
* `Stacks.Sheaves.RingedToposModules.toposModulesHomEquiv` and
  `inverseImageAdjDirectImageModules` (Stacks 03D3): for a morphism of topoi, the inverse
  image of sheaves of modules is left adjoint to the direct image.
* `Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction` (Stacks 03CZ):
  extension of scalars is left adjoint to restriction of scalars.
* `Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules` (Stacks 03D7, ringed
  topoi): pullback of sheaves of modules along a morphism of ringed topoi is left adjoint to
  pushforward.
* `Stacks.Sheaves.RingedToposModules.moduleSheaf_pushforwardModules` and
  `pushforwardModules_smul`: the pushforward functor is the one Stacks 03D6 part (1)
  prescribes — its underlying sheaf is the direct image, and its action is the restriction
  along `f♯` of the direct-image action of Stacks 03D1.

## Implementation notes

Stacks 03D3 is proved here for an arbitrary morphism of topoi, not only for one coming from
a morphism of sites. There is no description of `f⁻¹` or `f_*` on sections, so a morphism of
sheaves of modules cannot be transported by hand; instead the two linearity conditions are
written as commuting squares of morphisms of sheaves of sets (`moduleAddHom_comp_iff`,
`moduleSMulHom_comp_iff`) and transported across the hom-set bijection of `f⁻¹ ⊣ f_*` by
`homEquiv_binary_iff`. Because that transport is an `iff`, the bijection is obtained in both
directions at once, which is the implication the source leaves out ("we omit the proof of the
implication `β` linear ⇒ `α` linear"). The ring map along which the direct image is restricted
is `Stacks.Sheaves.ToposPushforward.ringUnit`, the unit `O ⟶ f_*f⁻¹O` as a map of sheaves of
rings; the adjunct of the identity of `f⁻¹O` is exactly that unit
(`homEquiv_id_eq_ringUnit`), which is why the inverse image of the scalar multiplication
transports to the restricted one.

Extension of scalars is built from the presheaf-level tensor product of Stacks 03CU followed
by Mathlib's sheafification of presheaves of modules, and the sheaf-level adjunction is
obtained from the presheaf-level one by
`CategoryTheory.Adjunction.restrictFullyFaithful` along the fully faithful inclusion of
sheaves of modules into presheaves of modules. Mathlib's own change-of-rings left adjoint for
sheaves of modules is available only for small sites whose objects, morphisms and sections all
lie in one universe, because it is obtained from
`PresheafOfModules.pullbackObjIsDefined_eq_top`; no such restriction is imposed here. Stacks
03CU is stated for presheaves of *commutative* rings, so the inverse-image ring has to be
produced as a presheaf of commutative rings: `inverseImageCommRingPresheaf` transports the
commutativity of the multiplication through the inverse image
(`ringMulHom_comm`, `ringMulObj_comm`) and is set up so that forgetting commutativity returns
`Stacks.Sheaves.ToposPullback.pullbackRingPresheaf` on the nose
(`ringPresheaf_inverseImageCommRingPresheaf`), so that the two categories of sheaves of
modules involved are literally the same.

`RingedToposHom` records the structure map in both forms, `f♯ : O_D ⟶ f_*O_C` and
`f⁻¹O_D ⟶ O_C`, together with the requirement that they be adjunct on underlying sheaves of
sets. Stacks 01D3 part (2) takes only the direct-image form as data, the inverse-image form
(which is the one Stacks 03D6 part (2) uses) being recovered from it by the adjunction
`f⁻¹ ⊣ f_*` for sheaves of rings, i.e. by Stacks 00YV. That instance of 00YV for sheaves of
rings is not available in this development, so the two forms and their compatibility are
carried as data; this is the same notion, presented so that neither form has to be
constructed from the other.

Accordingly `pushforwardModules` is defined as "restrict to `f⁻¹O_D`, push forward, restrict
along the unit", which is the composite the adjunction produces, and the two lemmas
`moduleSheaf_pushforwardModules` and `pushforwardModules_smul` identify it with the functor
Stacks 03D6 part (1) describes: its underlying sheaf of sets is the direct image, and its
action is the restriction along `f♯` of the direct-image action of Stacks 03D1. Those two
facts pin the sheaf of modules down completely. The alternative, defining the functor as
`f_*` followed by restriction along `f♯` and then comparing the two by an isomorphism, was
tried and is not viable: the two module structures are definitionally equal but the kernel
does not check it in reasonable time, the comparison going through the transported additive
structure of every direct image.

The two topoi have independent universes throughout: the objects, morphisms and sections of
the source and of the target site are unrelated, and the sections of a sheaf of modules lie
in the universe of the sections of its sheaf of rings, as in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ToposPullback.lean`. Nothing is asserted at a
narrower universe than the statement supports.

## References

* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D3](https://stacks.math.columbia.edu/tag/03D3)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
-/

@[expose] public section

open CategoryTheory Limits

namespace Stacks.Sheaves.RingedToposModules

/-! ## Adjuncts of squares built from finite products -/

section Adjunct

universe v u v' u'

variable {E : Type u} [Category.{v} E] {F : Type u'} [Category.{v'} F]
  [HasFiniteProducts E] [HasFiniteProducts F]
  {Φ : F ⥤ E} {Ψ : E ⥤ F} (adj : Φ ⊣ Ψ)

/-- The adjunct of the product comparison of `Φ` followed by a product of two morphisms is
the product of their adjuncts, followed by the inverse of the product comparison of `Ψ`.
Stated as a compatibility with the product comparison of `Ψ`, so that no inverse appears. -/
lemma homEquiv_prodComparison_prodMap {A₁ A₂ : F} {B₁ B₂ : E}
    (a₁ : Φ.obj A₁ ⟶ B₁) (a₂ : Φ.obj A₂ ⟶ B₂) :
    adj.homEquiv (A₁ ⨯ A₂) (B₁ ⨯ B₂) (prodComparison Φ A₁ A₂ ≫ prod.map a₁ a₂) ≫
        prodComparison Ψ B₁ B₂ =
      prod.map (adj.homEquiv A₁ B₁ a₁) (adj.homEquiv A₂ B₂ a₂) := by
  refine prod.hom_ext ?_ ?_
  · rw [Category.assoc, prodComparison_fst, ← adj.homEquiv_naturality_right,
      Category.assoc, prod.map_fst, ← Category.assoc, prodComparison_fst,
      adj.homEquiv_naturality_left, prod.map_fst]
  · rw [Category.assoc, prodComparison_snd, ← adj.homEquiv_naturality_right,
      Category.assoc, prod.map_snd, ← Category.assoc, prodComparison_snd,
      adj.homEquiv_naturality_left, prod.map_snd]

/-- A square expressing that a morphism `a : Φ A ⟶ B` is compatible with a binary operation
`m` on the source and `n` on the target holds if and only if the corresponding square for the
adjunct of `a` holds. The morphism `n'` is the operation transported to `Ψ`, specified by its
compatibility `hn` with the product comparison. -/
lemma homEquiv_binary_iff {A A₁ A₂ : F} {B B₁ B₂ : E} (a : Φ.obj A ⟶ B)
    (a₁ : Φ.obj A₁ ⟶ B₁) (a₂ : Φ.obj A₂ ⟶ B₂) (m : A₁ ⨯ A₂ ⟶ A) (n : B₁ ⨯ B₂ ⟶ B)
    (n' : Ψ.obj B₁ ⨯ Ψ.obj B₂ ⟶ Ψ.obj B) (hn : prodComparison Ψ B₁ B₂ ≫ n' = Ψ.map n) :
    Φ.map m ≫ a = prodComparison Φ A₁ A₂ ≫ prod.map a₁ a₂ ≫ n ↔
      m ≫ adj.homEquiv A B a =
        prod.map (adj.homEquiv A₁ B₁ a₁) (adj.homEquiv A₂ B₂ a₂) ≫ n' := by
  rw [← Equiv.apply_eq_iff_eq (adj.homEquiv (A₁ ⨯ A₂) B), adj.homEquiv_naturality_left,
    ← Category.assoc, adj.homEquiv_naturality_right, ← hn, ← Category.assoc,
    homEquiv_prodComparison_prodMap adj]

/-- Precomposing with the product comparison, an isomorphism, does not change whether a square
with the transported operation holds. -/
private lemma comp_eq_iff_prodComparison_comp {A A₁ A₂ : F} {B : E} [IsIso (prodComparison Φ A₁ A₂)]
    (m : A₁ ⨯ A₂ ⟶ A) (m' : Φ.obj A₁ ⨯ Φ.obj A₂ ⟶ Φ.obj A)
    (hm : Φ.map m = prodComparison Φ A₁ A₂ ≫ m') (a : Φ.obj A ⟶ B)
    (t : Φ.obj A₁ ⨯ Φ.obj A₂ ⟶ B) :
    m' ≫ a = t ↔ Φ.map m ≫ a = prodComparison Φ A₁ A₂ ≫ t := by
  rw [hm, Category.assoc, cancel_epi]

end Adjunct

/-! ## Morphisms of sheaves of modules as morphisms of the underlying sheaves of sets -/

section ModuleHom

universe t w v u

open CategoryTheory.Functor CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  {R : Sheaf J RingCat.{w}} {M N : SheafOfModules.{w} R}

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- A morphism of sheaves of modules is determined by the induced morphism of the underlying
sheaves of sets. -/
lemma hom_ext_moduleSheafFunctor {α β : M ⟶ N}
    (h : (Sheaf.moduleSheafFunctor R).map α = (Sheaf.moduleSheafFunctor R).map β) : α = β := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun X ↦
    ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_))
  exact congrArg
    (fun m : Sheaf.moduleSheaf R M ⟶ Sheaf.moduleSheaf R N ↦ m.hom.app X x) h

/-- A morphism of the underlying sheaves of sets which is additive and compatible with scalar
multiplication on sections over every object of the site is a morphism of sheaves of
modules. -/
noncomputable def ofSheafHom (s : Sheaf.moduleSheaf R M ⟶ Sheaf.moduleSheaf R N)
    (hadd : ∀ (X : Cᵒᵖ) (x y : (Sheaf.sectionsFunctor J X).obj (Sheaf.moduleSheaf R M)),
      (Sheaf.sectionsFunctor J X).map s (x + y) =
        (Sheaf.sectionsFunctor J X).map s x + (Sheaf.sectionsFunctor J X).map s y)
    (hsmul : ∀ (X : Cᵒᵖ) (r : (Sheaf.sectionsFunctor J X).obj (Sheaf.ringSheaf R))
      (x : (Sheaf.sectionsFunctor J X).obj (Sheaf.moduleSheaf R M)),
      (Sheaf.sectionsFunctor J X).map s (r • x) = r • (Sheaf.sectionsFunctor J X).map s x) :
    M ⟶ N where
  val := PresheafOfModules.homMk
    { app := fun X ↦ AddCommGrpCat.ofHom
        (AddMonoidHom.mk' ((Sheaf.sectionsFunctor J X).map s) (hadd X))
      naturality := fun {X Y} g ↦ by
        refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x ↦ ?_)
        exact (natTrans_app_map_apply (Sheaf.sectionsRestrict g) s x).symm } hsmul

@[simp]
lemma moduleSheafFunctor_map_ofSheafHom
    (s : Sheaf.moduleSheaf R M ⟶ Sheaf.moduleSheaf R N) (hadd) (hsmul) :
    (Sheaf.moduleSheafFunctor R).map (ofSheafHom s hadd hsmul) = s := rfl

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- The left-hand side of the additivity equation, read on a pair of sections. -/
lemma sectionsFunctor_map_moduleAddHom_comp (s : Sheaf.moduleSheaf R M ⟶ Sheaf.moduleSheaf R N)
    (X : Cᵒᵖ) (x y : (Sheaf.sectionsFunctor J X).obj (Sheaf.moduleSheaf R M)) :
    (Sheaf.sectionsFunctor J X).map (Sheaf.moduleAddHom R M ≫ s) (prodObjMk x y) =
      (Sheaf.sectionsFunctor J X).map s (x + y) := by
  rw [(Sheaf.sectionsFunctor J X).map_comp_apply, Sheaf.sectionsFunctor_map_moduleAddHom]

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- The right-hand side of the additivity equation, read on a pair of sections. -/
lemma sectionsFunctor_map_prodMap_moduleAddHom
    (s : Sheaf.moduleSheaf R M ⟶ Sheaf.moduleSheaf R N)
    (X : Cᵒᵖ) (x y : (Sheaf.sectionsFunctor J X).obj (Sheaf.moduleSheaf R M)) :
    (Sheaf.sectionsFunctor J X).map (prod.map s s ≫ Sheaf.moduleAddHom R N)
        (prodObjMk x y) =
      (Sheaf.sectionsFunctor J X).map s x + (Sheaf.sectionsFunctor J X).map s y := by
  rw [(Sheaf.sectionsFunctor J X).map_comp_apply, map_prodMap_apply, map_fst_prodObjMk,
    map_snd_prodObjMk, Sheaf.sectionsFunctor_map_moduleAddHom]

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- A morphism of the underlying sheaves of sets is additive on sections exactly when it
commutes with the addition maps of the two sheaves of modules. -/
lemma moduleAddHom_comp_iff (s : Sheaf.moduleSheaf R M ⟶ Sheaf.moduleSheaf R N) :
    Sheaf.moduleAddHom R M ≫ s = prod.map s s ≫ Sheaf.moduleAddHom R N ↔
      ∀ (X : Cᵒᵖ) (x y : (Sheaf.sectionsFunctor J X).obj (Sheaf.moduleSheaf R M)),
        (Sheaf.sectionsFunctor J X).map s (x + y) =
          (Sheaf.sectionsFunctor J X).map s x + (Sheaf.sectionsFunctor J X).map s y := by
  constructor
  · intro h X x y
    rw [← sectionsFunctor_map_moduleAddHom_comp s X x y, h,
      sectionsFunctor_map_prodMap_moduleAddHom]
  · intro h
    refine Sheaf.hom_ext_sections fun X p ↦ ?_
    rw [← prodObjMk_map_fst_map_snd (P := Sheaf.sectionsFunctor J X) p,
      sectionsFunctor_map_moduleAddHom_comp, sectionsFunctor_map_prodMap_moduleAddHom]
    exact h X _ _

/-- The left-hand side of the scalar-multiplication equation, read on sections. -/
lemma sectionsFunctor_map_moduleSMulHom_comp (s : Sheaf.moduleSheaf R M ⟶ Sheaf.moduleSheaf R N)
    (X : Cᵒᵖ) (r : (Sheaf.sectionsFunctor J X).obj (Sheaf.ringSheaf R))
    (x : (Sheaf.sectionsFunctor J X).obj (Sheaf.moduleSheaf R M)) :
    (Sheaf.sectionsFunctor J X).map (Sheaf.moduleSMulHom R M ≫ s) (prodObjMk r x) =
      (Sheaf.sectionsFunctor J X).map s (r • x) := by
  rw [(Sheaf.sectionsFunctor J X).map_comp_apply, Sheaf.sectionsFunctor_map_moduleSMulHom]

/-- The right-hand side of the scalar-multiplication equation, read on sections. -/
lemma sectionsFunctor_map_prodMap_moduleSMulHom
    (s : Sheaf.moduleSheaf R M ⟶ Sheaf.moduleSheaf R N)
    (X : Cᵒᵖ) (r : (Sheaf.sectionsFunctor J X).obj (Sheaf.ringSheaf R))
    (x : (Sheaf.sectionsFunctor J X).obj (Sheaf.moduleSheaf R M)) :
    (Sheaf.sectionsFunctor J X).map
        (prod.map (𝟙 (Sheaf.ringSheaf R)) s ≫ Sheaf.moduleSMulHom R N) (prodObjMk r x) =
      r • (Sheaf.sectionsFunctor J X).map s x := by
  rw [(Sheaf.sectionsFunctor J X).map_comp_apply, map_prodMap_apply, map_fst_prodObjMk,
    map_snd_prodObjMk, (Sheaf.sectionsFunctor J X).map_id_apply,
    Sheaf.sectionsFunctor_map_moduleSMulHom]

/-- A morphism of the underlying sheaves of sets is compatible with scalar multiplication on
sections exactly when it commutes with the scalar-multiplication maps. -/
lemma moduleSMulHom_comp_iff (s : Sheaf.moduleSheaf R M ⟶ Sheaf.moduleSheaf R N) :
    Sheaf.moduleSMulHom R M ≫ s =
        prod.map (𝟙 (Sheaf.ringSheaf R)) s ≫ Sheaf.moduleSMulHom R N ↔
      ∀ (X : Cᵒᵖ) (r : (Sheaf.sectionsFunctor J X).obj (Sheaf.ringSheaf R))
        (x : (Sheaf.sectionsFunctor J X).obj (Sheaf.moduleSheaf R M)),
        (Sheaf.sectionsFunctor J X).map s (r • x) =
          r • (Sheaf.sectionsFunctor J X).map s x := by
  constructor
  · intro h X r x
    rw [← sectionsFunctor_map_moduleSMulHom_comp s X r x, h,
      sectionsFunctor_map_prodMap_moduleSMulHom]
  · intro h
    refine Sheaf.hom_ext_sections fun X p ↦ ?_
    rw [← prodObjMk_map_fst_map_snd (P := Sheaf.sectionsFunctor J X) p,
      sectionsFunctor_map_moduleSMulHom_comp, sectionsFunctor_map_prodMap_moduleSMulHom]
    exact h X _ _

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- Restriction of scalars does not change the addition map of the underlying sheaf of sets. -/
lemma moduleAddHom_restrictScalars {R' : Sheaf J RingCat.{w}} (α : R ⟶ R')
    (N' : SheafOfModules.{w} R') :
    Sheaf.moduleAddHom R ((SheafOfModules.restrictScalars α).obj N') =
      Sheaf.moduleAddHom R' N' := rfl

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- The additivity square for the underlying morphism of sheaves of sets of a morphism of
sheaves of modules. -/
lemma moduleAddHom_comp_moduleSheafFunctor_map (α : M ⟶ N) :
    Sheaf.moduleAddHom R M ≫ (Sheaf.moduleSheafFunctor R).map α =
      prod.map ((Sheaf.moduleSheafFunctor R).map α) ((Sheaf.moduleSheafFunctor R).map α) ≫
        Sheaf.moduleAddHom R N :=
  (moduleAddHom_comp_iff _).mpr fun X x y ↦
    Sheaf.sectionsFunctor_map_moduleSheafFunctor_map_add R α X x y

/-- The scalar-multiplication square for the underlying morphism of sheaves of sets of a
morphism of sheaves of modules. -/
lemma moduleSMulHom_comp_moduleSheafFunctor_map (α : M ⟶ N) :
    Sheaf.moduleSMulHom R M ≫ (Sheaf.moduleSheafFunctor R).map α =
      prod.map (𝟙 (Sheaf.ringSheaf R)) ((Sheaf.moduleSheafFunctor R).map α) ≫
        Sheaf.moduleSMulHom R N :=
  (moduleSMulHom_comp_iff _).mpr fun X r x ↦
    Sheaf.sectionsFunctor_map_moduleSheafFunctor_map_smul R α X r x

/-- Scalar multiplication on a sheaf of modules obtained by restriction of scalars is the
original scalar multiplication, with the scalars carried along the morphism of sheaves of
rings. This is the form in which the restriction appears in a square for a morphism of
sheaves of modules. -/
lemma prodMap_moduleSMulHom_restrictScalars {R' : Sheaf J RingCat.{w}} (α : R ⟶ R')
    {N' : SheafOfModules.{w} R'} (b : Sheaf.moduleSheaf R M ⟶ Sheaf.moduleSheaf R' N') :
    prod.map (𝟙 (Sheaf.ringSheaf R)) b ≫
        Sheaf.moduleSMulHom R ((SheafOfModules.restrictScalars α).obj N') =
      prod.map ((sheafCompose J (forget RingCat.{w})).map α) b ≫
        Sheaf.moduleSMulHom R' N' := by
  refine Sheaf.hom_ext_sections fun X p ↦ ?_
  change (Sheaf.sectionsFunctor J X).map
      (Sheaf.moduleSMulHom R ((SheafOfModules.restrictScalars α).obj N'))
      ((Sheaf.sectionsFunctor J X).map (prod.map (𝟙 (Sheaf.ringSheaf R)) b) p) =
    (Sheaf.sectionsFunctor J X).map (Sheaf.moduleSMulHom R' N')
      ((Sheaf.sectionsFunctor J X).map
        (prod.map ((sheafCompose J (forget RingCat.{w})).map α) b) p)
  rw [map_prodMap_apply, map_prodMap_apply, (Sheaf.sectionsFunctor J X).map_id_apply,
    Sheaf.sectionsFunctor_map_moduleSMulHom]
  exact Sheaf.sectionsFunctor_map_moduleSMulHom R
    ((SheafOfModules.restrictScalars α).obj N') X _ _

/-- Scalar multiplication on a sheaf of modules obtained by restriction of scalars is the
original one, with the scalars carried along the morphism of sheaves of rings. -/
lemma moduleSMulHom_restrictScalars {R' : Sheaf J RingCat.{w}} (α : R ⟶ R')
    (N' : SheafOfModules.{w} R') :
    Sheaf.moduleSMulHom R ((SheafOfModules.restrictScalars α).obj N') =
      prod.map ((sheafCompose J (forget RingCat.{w})).map α)
          (𝟙 (Sheaf.moduleSheaf R ((SheafOfModules.restrictScalars α).obj N'))) ≫
        Sheaf.moduleSMulHom R' N' := by
  refine Sheaf.hom_ext_sections fun X p ↦ ?_
  change (Sheaf.sectionsFunctor J X).map
      (Sheaf.moduleSMulHom R ((SheafOfModules.restrictScalars α).obj N')) p =
    (Sheaf.sectionsFunctor J X).map (Sheaf.moduleSMulHom R' N')
      ((Sheaf.sectionsFunctor J X).map
        (prod.map ((sheafCompose J (forget RingCat.{w})).map α)
          (𝟙 (Sheaf.moduleSheaf R ((SheafOfModules.restrictScalars α).obj N')))) p)
  rw [← prodObjMk_map_fst_map_snd (P := Sheaf.sectionsFunctor J X) p, map_prodMap_apply,
    map_fst_prodObjMk, map_snd_prodObjMk, (Sheaf.sectionsFunctor J X).map_id_apply,
    Sheaf.sectionsFunctor_map_moduleSMulHom]
  exact (Sheaf.sectionsFunctor_map_moduleSMulHom R' N' X _ _).symm

/-- Scalar multiplication transported along a finite-product-preserving functor to types,
for a sheaf of modules obtained by restriction of scalars. -/
lemma moduleSMulObj_restrictScalars {R' : Sheaf J RingCat.{w}} (α : R ⟶ R')
    (N' : SheafOfModules.{w} R') (P : Sheaf J (Type w) ⥤ Type t) [PreservesFiniteProducts P]
    (r : P.obj (Sheaf.ringSheaf R))
    (m : P.obj (Sheaf.moduleSheaf R ((SheafOfModules.restrictScalars α).obj N'))) :
    Sheaf.moduleSMulObj R ((SheafOfModules.restrictScalars α).obj N') P r m =
      Sheaf.moduleSMulObj R' N' P
        (P.map ((sheafCompose J (forget RingCat.{w})).map α) r) m := by
  have h := (congrArg
    (fun n ↦ P.map n (prodObjMk (P := P) (A := Sheaf.ringSheaf R)
      (B := Sheaf.moduleSheaf R ((SheafOfModules.restrictScalars α).obj N')) r m))
    (moduleSMulHom_restrictScalars α N')).trans (P.map_comp_apply _ _ _)
  rw [map_prodMap_apply, map_fst_prodObjMk, map_snd_prodObjMk,
    CategoryTheory.Functor.map_id_apply] at h
  exact h

/-- A morphism of sheaves of modules is the same thing as a morphism of the underlying
sheaves of sets which commutes with the addition maps and with the scalar-multiplication
maps. -/
noncomputable def homEquivSubtype :
    (M ⟶ N) ≃ {s : Sheaf.moduleSheaf R M ⟶ Sheaf.moduleSheaf R N //
      Sheaf.moduleAddHom R M ≫ s = prod.map s s ≫ Sheaf.moduleAddHom R N ∧
        Sheaf.moduleSMulHom R M ≫ s =
          prod.map (𝟙 (Sheaf.ringSheaf R)) s ≫ Sheaf.moduleSMulHom R N} where
  toFun α := ⟨(Sheaf.moduleSheafFunctor R).map α,
    moduleAddHom_comp_moduleSheafFunctor_map α, moduleSMulHom_comp_moduleSheafFunctor_map α⟩
  invFun s := ofSheafHom s.1 ((moduleAddHom_comp_iff _).mp s.2.1)
    ((moduleSMulHom_comp_iff _).mp s.2.2)
  left_inv _ := hom_ext_moduleSheafFunctor rfl
  right_inv _ := Subtype.ext rfl

@[simp]
lemma moduleSheafFunctor_map_homEquivSubtype_symm
    (s : {s : Sheaf.moduleSheaf R M ⟶ Sheaf.moduleSheaf R N //
      Sheaf.moduleAddHom R M ≫ s = prod.map s s ≫ Sheaf.moduleAddHom R N ∧
        Sheaf.moduleSMulHom R M ≫ s =
          prod.map (𝟙 (Sheaf.ringSheaf R)) s ≫ Sheaf.moduleSMulHom R N}) :
    (Sheaf.moduleSheafFunctor R).map (homEquivSubtype.symm s) = s.1 := rfl

end ModuleHom


/-! ## Inverse image and direct image of sheaves of modules along a morphism of topoi -/

section ToposModules

universe w w' v u v' u'

open CategoryTheory.Functor CategoryTheory.Sheaf
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{w'})]
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))
  (O : Sheaf K RingCat.{w'})

/-- The inverse image of sheaves of modules along a morphism of topoi, as a functor to
sheaves of modules over the inverse-image sheaf of rings. This is Stacks 03D2. -/
noncomputable abbrev inverseImageModules :
    SheafOfModules.{w'} O ⥤ SheafOfModules.{w} (inverseImageRingSheaf f O) :=
  pullbackModuleFunctor J f.inverseImage O

/-- The direct image of a sheaf of modules over the inverse-image sheaf of rings, read as a
sheaf of `O`-modules by restriction of scalars along the unit `O ⟶ f_*f⁻¹O`. This is the
right-hand side of the adjunction of Stacks 03D3: the direct image of sheaves of modules
restricted along the unit, `Stacks.Sheaves.ToposPushforward.pushforwardModulesAlong`. -/
noncomputable abbrev directImageModules :
    SheafOfModules.{w} (inverseImageRingSheaf f O) ⥤ SheafOfModules.{w'} O :=
  pushforwardModulesAlong f (inverseImageRingSheaf f O) (ringUnit f O)

omit [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{w'})] in
/-- The underlying morphism of sheaves of sets of the unit `O ⟶ f_*f⁻¹O` is the unit of the
adjunction `f⁻¹ ⊣ f_*` at the underlying sheaf of sets of `O`. -/
lemma ringSheafMap_ringUnit :
    (sheafCompose K (forget RingCat.{w'})).map (ringUnit f O) =
      f.adj.unit.app (Sheaf.ringSheaf O) :=
  Sheaf.hom_ext_sections fun _ _ ↦ rfl

omit [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{w'})] in
/-- The adjunct of the identity of the inverse-image ring is the unit `O ⟶ f_*f⁻¹O`. -/
lemma homEquiv_id_eq_ringUnit :
    f.adj.homEquiv (Sheaf.ringSheaf O) (Sheaf.ringSheaf (inverseImageRingSheaf f O))
        (𝟙 (Sheaf.ringSheaf (inverseImageRingSheaf f O))) =
      (sheafCompose K (forget RingCat.{w'})).map (ringUnit f O) :=
  (f.adj.homEquiv_id (Sheaf.ringSheaf O)).trans (ringSheafMap_ringUnit f O).symm

omit [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{w'})] in
/-- The binary-product comparison of the inverse image of a morphism of topoi is an
isomorphism, the inverse image being left exact. -/
lemma isIso_prodComparison_inverseImage (A B : Sheaf K (Type w')) :
    IsIso (prodComparison f.inverseImage A B) := by
  rw [← PreservesLimitPair.iso_hom]
  infer_instance

variable {G G' : SheafOfModules.{w'} O} {F F' : SheafOfModules.{w} (inverseImageRingSheaf f O)}

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- The underlying morphism of sheaves of sets of an inverse image of a morphism of sheaves of
modules is the inverse image of the underlying morphism. -/
lemma moduleSheafFunctor_map_inverseImageModules_map (φ : G ⟶ G') :
    (Sheaf.moduleSheafFunctor (inverseImageRingSheaf f O)).map
        ((inverseImageModules f O).map φ) =
      f.inverseImage.map ((Sheaf.moduleSheafFunctor O).map φ) :=
  Sheaf.hom_ext_sections fun X x ↦
    pullbackModuleMap_val_app_apply J f.inverseImage O φ X x

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- **Taking the inverse image of a sheaf of modules does not change the underlying sheaf of
sets**: `f⁻¹𝒢 ≅ f⁻¹|𝒢|`, as an isomorphism of functors to sheaves of sets. The two sides are
the same object and the same morphism of sheaves of sets, by
`moduleSheafFunctor_map_inverseImageModules_map`; what the bundled isomorphism adds is a
morphism of the two spellings, so that a composition crossing from one to the other is
syntactically well formed and can be rewritten. -/
noncomputable def inverseImageModuleSheafIso :
    inverseImageModules f O ⋙ Sheaf.moduleSheafFunctor (inverseImageRingSheaf f O) ≅
      Sheaf.moduleSheafFunctor O ⋙ f.inverseImage :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun {_ _} φ ↦
    (Category.comp_id _).trans
      ((moduleSheafFunctor_map_inverseImageModules_map f O φ).trans (Category.id_comp _).symm)

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- The comparison of the underlying sheaf of sets of an inverse image with the inverse image of
the underlying sheaf of sets is the identity. -/
@[simp]
lemma inverseImageModuleSheafIso_hom_app (G : SheafOfModules.{w'} O) :
    (inverseImageModuleSheafIso f O).hom.app G = 𝟙 _ :=
  rfl

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- The backward comparison of the underlying sheaf of sets of an inverse image with the
inverse image of the underlying sheaf of sets is the identity. -/
@[simp]
lemma inverseImageModuleSheafIso_inv_app (G : SheafOfModules.{w'} O) :
    (inverseImageModuleSheafIso f O).inv.app G = 𝟙 _ :=
  rfl

/-- The underlying morphism of sheaves of sets of a direct image of a morphism of sheaves of
modules is the direct image of the underlying morphism. -/
lemma moduleSheafFunctor_map_directImageModules_map (ψ : F ⟶ F') :
    (Sheaf.moduleSheafFunctor O).map ((directImageModules f O).map ψ) =
      f.pushforward.map ((Sheaf.moduleSheafFunctor (inverseImageRingSheaf f O)).map ψ) :=
  Sheaf.hom_ext_sections fun X x ↦
    pullbackModuleMap_val_app_apply K f.pushforward (inverseImageRingSheaf f O) ψ X x

/-- Additivity of a morphism out of an inverse-image sheaf of modules is equivalent to
additivity of its adjunct. -/
lemma homEquiv_moduleAddHom_iff
    (a : Sheaf.moduleSheaf (inverseImageRingSheaf f O) ((inverseImageModules f O).obj G) ⟶
      Sheaf.moduleSheaf (inverseImageRingSheaf f O) F) :
    Sheaf.moduleAddHom (inverseImageRingSheaf f O) ((inverseImageModules f O).obj G) ≫ a =
        prod.map a a ≫ Sheaf.moduleAddHom (inverseImageRingSheaf f O) F ↔
      Sheaf.moduleAddHom O G ≫ f.adj.homEquiv _ _ a =
        prod.map (f.adj.homEquiv _ _ a) (f.adj.homEquiv _ _ a) ≫
          Sheaf.moduleAddHom O ((directImageModules f O).obj F) := by
  refine Iff.trans ?_ (homEquiv_binary_iff f.adj a a a (Sheaf.moduleAddHom O G)
    (Sheaf.moduleAddHom (inverseImageRingSheaf f O) F) _
    (moduleAdd_map_aux' K f.pushforward (inverseImageRingSheaf f O) F).symm)
  have := isIso_prodComparison_inverseImage f (Sheaf.moduleSheaf O G) (Sheaf.moduleSheaf O G)
  exact comp_eq_iff_prodComparison_comp (Φ := f.inverseImage) _ _
    (moduleAdd_map_aux' J f.inverseImage O G) a _

/-- Compatibility with scalar multiplication for a morphism out of an inverse-image sheaf of
modules is equivalent to the same compatibility for its adjunct, the scalars on the target
side acting through the unit `O ⟶ f_*f⁻¹O`. -/
lemma homEquiv_moduleSMulHom_iff
    (a : Sheaf.moduleSheaf (inverseImageRingSheaf f O) ((inverseImageModules f O).obj G) ⟶
      Sheaf.moduleSheaf (inverseImageRingSheaf f O) F) :
    Sheaf.moduleSMulHom (inverseImageRingSheaf f O) ((inverseImageModules f O).obj G) ≫ a =
        prod.map (𝟙 (Sheaf.ringSheaf (inverseImageRingSheaf f O))) a ≫
          Sheaf.moduleSMulHom (inverseImageRingSheaf f O) F ↔
      Sheaf.moduleSMulHom O G ≫ f.adj.homEquiv _ _ a =
        prod.map (𝟙 (Sheaf.ringSheaf O)) (f.adj.homEquiv _ _ a) ≫
          Sheaf.moduleSMulHom O ((directImageModules f O).obj F) := by
  have key : prod.map (𝟙 (Sheaf.ringSheaf O)) (f.adj.homEquiv _ _ a) ≫
        Sheaf.moduleSMulHom O ((directImageModules f O).obj F) =
      prod.map ((sheafCompose K (forget RingCat.{w'})).map (ringUnit f O))
          (f.adj.homEquiv _ _ a) ≫
        Sheaf.moduleSMulHom (pushforwardRingSheaf f (inverseImageRingSheaf f O))
          ((pushforwardModuleFunctor f (inverseImageRingSheaf f O)).obj F) :=
    prodMap_moduleSMulHom_restrictScalars (ringUnit f O) _
  rw [key, ← homEquiv_id_eq_ringUnit]
  refine Iff.trans ?_ (homEquiv_binary_iff f.adj a
    (𝟙 (Sheaf.ringSheaf (inverseImageRingSheaf f O))) a (Sheaf.moduleSMulHom O G)
    (Sheaf.moduleSMulHom (inverseImageRingSheaf f O) F) _
    (moduleSMul_map_aux' K f.pushforward (inverseImageRingSheaf f O) F).symm)
  have := isIso_prodComparison_inverseImage f (Sheaf.ringSheaf O) (Sheaf.moduleSheaf O G)
  exact comp_eq_iff_prodComparison_comp (Φ := f.inverseImage) _ _
    (moduleSMul_map_aux' J f.inverseImage O G) a _

/-- **Stacks 03D3**: the canonical bijection between morphisms out of an inverse-image sheaf
of modules and morphisms into the direct image, the latter read as a sheaf of `O`-modules by
restriction of scalars along the unit `O ⟶ f_*f⁻¹O`. -/
@[stacks 03D3 "the canonical bijection `Hom_{f⁻¹O}(f⁻¹G, F) = Hom_O(G, f_*F)` itself"]
noncomputable def toposModulesHomEquiv (G : SheafOfModules.{w'} O)
    (F : SheafOfModules.{w} (inverseImageRingSheaf f O)) :
    ((inverseImageModules f O).obj G ⟶ F) ≃ (G ⟶ (directImageModules f O).obj F) :=
  (homEquivSubtype (R := inverseImageRingSheaf f O)
      (M := (inverseImageModules f O).obj G) (N := F)).trans
    ((Equiv.subtypeEquiv (f.adj.homEquiv (Sheaf.moduleSheaf O G)
        (Sheaf.moduleSheaf (inverseImageRingSheaf f O) F)) fun a ↦
          and_congr (homEquiv_moduleAddHom_iff f O a) (homEquiv_moduleSMulHom_iff f O a)).trans
      (homEquivSubtype (R := O) (M := G) (N := (directImageModules f O).obj F)).symm)

@[simp]
lemma moduleSheafFunctor_map_toposModulesHomEquiv
    (α : (inverseImageModules f O).obj G ⟶ F) :
    (Sheaf.moduleSheafFunctor O).map (toposModulesHomEquiv f O G F α) =
      f.adj.homEquiv (Sheaf.moduleSheaf O G)
        (Sheaf.moduleSheaf (inverseImageRingSheaf f O) F)
          ((Sheaf.moduleSheafFunctor (inverseImageRingSheaf f O)).map α) := rfl

@[simp]
lemma moduleSheafFunctor_map_toposModulesHomEquiv_symm
    (β : G ⟶ (directImageModules f O).obj F) :
    (Sheaf.moduleSheafFunctor (inverseImageRingSheaf f O)).map
        ((toposModulesHomEquiv f O G F).symm β) =
      (f.adj.homEquiv (Sheaf.moduleSheaf O G)
        (Sheaf.moduleSheaf (inverseImageRingSheaf f O) F)).symm
          ((Sheaf.moduleSheafFunctor O).map β) := rfl

/-- **Stacks 03D3** as an adjunction: the inverse image of sheaves of modules along a
morphism of topoi is left adjoint to the direct image, read as a sheaf of `O`-modules by
restriction of scalars along the unit `O ⟶ f_*f⁻¹O`. -/
@[stacks 03D3 "the bijection as an adjunction, hence natural in both variables"]
noncomputable def inverseImageAdjDirectImageModules :
    inverseImageModules f O ⊣ directImageModules f O :=
  Adjunction.mkOfHomEquiv
    { homEquiv := toposModulesHomEquiv f O
      homEquiv_naturality_left_symm := fun {G' G F} g β ↦ by
        have h := f.adj.homEquiv_naturality_left_symm
          (Y := Sheaf.moduleSheaf (inverseImageRingSheaf f O) F)
          ((Sheaf.moduleSheafFunctor O).map g) ((Sheaf.moduleSheafFunctor O).map β)
        refine hom_ext_moduleSheafFunctor ?_
        rw [moduleSheafFunctor_map_toposModulesHomEquiv_symm, CategoryTheory.Functor.map_comp,
          CategoryTheory.Functor.map_comp, moduleSheafFunctor_map_toposModulesHomEquiv_symm,
          moduleSheafFunctor_map_inverseImageModules_map]
        exact h
      homEquiv_naturality_right := fun {G F F'} α k ↦ by
        have h := f.adj.homEquiv_naturality_right
          ((Sheaf.moduleSheafFunctor (inverseImageRingSheaf f O)).map α)
          ((Sheaf.moduleSheafFunctor (inverseImageRingSheaf f O)).map k)
        refine hom_ext_moduleSheafFunctor ?_
        rw [moduleSheafFunctor_map_toposModulesHomEquiv, CategoryTheory.Functor.map_comp,
          CategoryTheory.Functor.map_comp, moduleSheafFunctor_map_toposModulesHomEquiv,
          moduleSheafFunctor_map_directImageModules_map]
        exact h }

/-- **The unit of the Stacks 03D3 adjunction on sheaves of modules is the unit on sheaves of
sets**, on underlying sheaves.  The hom-set bijection of Stacks 03D3 sends a morphism to the
transpose of its underlying morphism of sheaves of sets, so its value at the identity — which is
what the unit of an adjunction presented by a hom-set bijection is — is the transpose of the
identity, namely the unit of `f⁻¹ ⊣ f_*`. -/
theorem moduleSheafFunctor_map_inverseImageAdjDirectImageModules_unit_app'
    (N : SheafOfModules.{w'} O) :
    (Sheaf.moduleSheafFunctor O).map ((inverseImageAdjDirectImageModules f O).unit.app N) =
      f.adj.unit.app (Sheaf.moduleSheaf O N) := by
  change (Sheaf.moduleSheafFunctor O).map
      (toposModulesHomEquiv f O N ((inverseImageModules f O).obj N) (𝟙 _)) = _
  rw [moduleSheafFunctor_map_toposModulesHomEquiv]
  change (f.adj.homEquiv (Sheaf.moduleSheaf O N)
    (Sheaf.moduleSheaf (inverseImageRingSheaf f O)
      ((inverseImageModules f O).obj N))) (𝟙 _) = _
  exact f.adj.homEquiv_id _

end ToposModules

/-! ## Extension and restriction of scalars for sheaves of modules on a site -/

section ChangeOfRings

universe w v u

open scoped TensorProduct

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- A presheaf of commutative rings whose underlying presheaf of rings is a sheaf, read as a
sheaf of rings. -/
abbrev commRingSheaf (A : Cᵒᵖ ⥤ CommRingCat.{w})
    (h : Presheaf.IsSheaf J (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf A)) : Sheaf J
      RingCat.{w} :=
  ⟨Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf A, h⟩

variable {A₁ A₂ : Cᵒᵖ ⥤ CommRingCat.{w}} (θ : A₁ ⟶ A₂)
  (h₁ : Presheaf.IsSheaf J (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf A₁))
  (h₂ : Presheaf.IsSheaf J (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf A₂))

/-- The morphism of sheaves of rings underlying a morphism of presheaves of commutative
rings. -/
def commRingSheafMap : commRingSheaf J A₁ h₁ ⟶ commRingSheaf J A₂ h₂ :=
  ⟨Functor.whiskerRight θ (forget₂ CommRingCat.{w} RingCat.{w})⟩

variable [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Extension of scalars for sheaves of modules along a morphism of sheaves of commutative
rings: the sectionwise tensor product `A₂ ⊗[A₁] -`, sheafified. This is the functor
`Mod(O₁) ⟶ Mod(O₂)` of Stacks 03CZ. -/
noncomputable def extendScalars :
    SheafOfModules.{w} (commRingSheaf J A₁ h₁) ⥤ SheafOfModules.{w} (commRingSheaf J A₂ h₂) :=
  SheafOfModules.forget (commRingSheaf J A₁ h₁) ⋙
    Stacks.PresheafOfModules.ChangeOfRings.changeOfRings θ ⋙
    PresheafOfModules.sheafification (R := commRingSheaf J A₂ h₂) (𝟙 _)

/-- **Stacks 03CZ**: extension of scalars is left adjoint to restriction of scalars.

Built from the explicit presheaf-level adjunction
  `Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsAdjunction`, so that
the sections of the unit are computable; see
`Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction_unit_app_val_app_apply`. -/
noncomputable def extendRestrictScalarsAdjunction :
    extendScalars J θ h₁ h₂ ⊣ SheafOfModules.restrictScalars (commRingSheafMap J θ h₁ h₂) :=
  Adjunction.restrictFullyFaithful
    ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsAdjunction θ).comp
      (PresheafOfModules.sheafificationAdjunction (R := commRingSheaf J A₂ h₂) (𝟙 _)))
    (SheafOfModules.fullyFaithfulForget (commRingSheaf J A₁ h₁))
    (Functor.FullyFaithful.id _)
    (eqToIso (Functor.comp_id (extendScalars J θ h₁ h₂)).symm) (eqToIso (Functor.id_comp _))

/-- The unit of `extendRestrictScalarsAdjunction`, as a morphism of presheaves of modules, is
the unit of the presheaf-level change of rings followed by the unit of sheafification. -/
theorem forget_map_extendRestrictScalarsAdjunction_unit_app
    (L : SheafOfModules.{w} (commRingSheaf J A₁ h₁)) :
    (SheafOfModules.forget (commRingSheaf J A₁ h₁)).map
        ((extendRestrictScalarsAdjunction J θ h₁ h₂).unit.app L) =
      (Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsAdjunction θ).unit.app L.val ≫
        (Stacks.PresheafOfModules.ChangeOfRings.restrictScalars θ).map
          ((PresheafOfModules.sheafificationAdjunction
              (R := commRingSheaf J A₂ h₂) (𝟙 _)).unit.app
            ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings θ).obj L.val)) := by
  rw [extendRestrictScalarsAdjunction, Adjunction.map_restrictFullyFaithful_unit_app,
    Adjunction.comp_unit_app]
  rfl

/-- The sections of the unit of `extendRestrictScalarsAdjunction` over an object `V`: a section
`x` of `L` is sent to the image of `1 ⊗ x` under the map to the sheafification. -/
theorem extendRestrictScalarsAdjunction_unit_app_val_app_apply
    (L : SheafOfModules.{w} (commRingSheaf J A₁ h₁)) (V : Cᵒᵖ) (x : L.val.obj V) :
    (((extendRestrictScalarsAdjunction J θ h₁ h₂).unit.app L).val.app V).hom x =
      letI := (θ.app V).hom.toAlgebra
      (CategoryTheory.toSheafify J ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings θ).obj
        L.val).presheaf).app V
        ((1 : A₂.obj V) ⊗ₜ[A₁.obj V] x) := by
  rw [show ((extendRestrictScalarsAdjunction J θ h₁ h₂).unit.app L).val
      = (SheafOfModules.forget (commRingSheaf J A₁ h₁)).map
          ((extendRestrictScalarsAdjunction J θ h₁ h₂).unit.app L) from rfl,
    forget_map_extendRestrictScalarsAdjunction_unit_app, PresheafOfModules.comp_app]
  rw (transparency := .default) [ModuleCat.hom_comp, LinearMap.comp_apply,
    Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsAdjunction_unit_app_apply]

end ChangeOfRings

/-! ## The inverse image of a sheaf of commutative rings -/

section CommutativeTransport

universe t w' v' u'

open CategoryTheory.Functor CategoryTheory.Sheaf

variable {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget RingCat.{w'})] (O : Sheaf K RingCat.{w'})
  (hcomm : ∀ (X : Dᵒᵖ) (a b : (Sheaf.sectionsFunctor K X).obj (Sheaf.ringSheaf O)),
    a * b = b * a)

set_option synthInstance.maxHeartbeats 400000 in
/- Instance search for this binary product otherwise times out exploring limits in
`Dᵒᵖ ⥤ RingCat`. -/
local instance : HasBinaryProducts (Sheaf K (Type w')) := inferInstance

noncomputable local instance : HasBinaryProduct (Sheaf.ringSheaf O) (Sheaf.ringSheaf O) :=
  HasLimitsOfShape.has_limit _

include hcomm in
/-- If the sections of a sheaf of rings commute, its multiplication map is symmetric. -/
lemma ringMulHom_comm :
    prod.lift (prod.snd : Sheaf.ringSheaf O ⨯ Sheaf.ringSheaf O ⟶ Sheaf.ringSheaf O) prod.fst ≫
        Sheaf.ringMulHom O =
      Sheaf.ringMulHom O := by
  refine Sheaf.hom_ext_sections fun X p ↦ ?_
  rw [← prodObjMk_map_fst_map_snd (P := Sheaf.sectionsFunctor K X) p,
    (Sheaf.sectionsFunctor K X).map_comp_apply, map_lift_apply, map_fst_prodObjMk,
    map_snd_prodObjMk, Sheaf.sectionsFunctor_map_ringMulHom,
    Sheaf.sectionsFunctor_map_ringMulHom]
  exact hcomm X _ _

include hcomm in
/-- The multiplication transported along a finite-product-preserving functor to types is
commutative when the original is. -/
lemma ringMulObj_comm (P : Sheaf K (Type w') ⥤ Type t) [PreservesFiniteProducts P]
    (x y : P.obj (Sheaf.ringSheaf O)) :
    Sheaf.ringMulObj O P x y = Sheaf.ringMulObj O P y x := by
  have h : P.map (prod.lift
        (prod.snd : Sheaf.ringSheaf O ⨯ Sheaf.ringSheaf O ⟶ Sheaf.ringSheaf O) prod.fst ≫
        Sheaf.ringMulHom O)
      (prodObjMk (P := P) (A := Sheaf.ringSheaf O) (B := Sheaf.ringSheaf O) x y) =
      P.map (Sheaf.ringMulHom O)
        (prodObjMk (P := P) (A := Sheaf.ringSheaf O) (B := Sheaf.ringSheaf O) x y) :=
    congrArg
      (fun m ↦ P.map m
        (prodObjMk (P := P) (A := Sheaf.ringSheaf O) (B := Sheaf.ringSheaf O) x y))
      (ringMulHom_comm O hcomm)
  rw [P.map_comp_apply, map_lift_apply, map_fst_prodObjMk, map_snd_prodObjMk] at h
  exact h.symm

end CommutativeTransport

section InverseImageCommRing

universe w w' v u v' u'

open CategoryTheory.Functor CategoryTheory.Sheaf
open Stacks.Sheaves.ToposPullback

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  (Φ : Sheaf K (Type w') ⥤ Sheaf J (Type w)) [PreservesFiniteProducts Φ]
  (O : Sheaf K RingCat.{w'})
  (hcomm : ∀ (X : Dᵒᵖ) (a b : (Sheaf.sectionsFunctor K X).obj (Sheaf.ringSheaf O)),
    a * b = b * a)

include hcomm in
omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- The sections of the inverse-image sheaf of rings over an object of the source site form a
commutative ring. -/
@[instance_reducible]
noncomputable def inverseImageSectionsCommRing (X : Cᵒᵖ) :
    CommRing ((Φ ⋙ Sheaf.sectionsFunctor J X).obj (Sheaf.ringSheaf O)) :=
  { Sheaf.ringObjRing O (Φ ⋙ Sheaf.sectionsFunctor J X) with
    mul_comm := fun a b ↦
      ringMulObj_comm O hcomm (Φ ⋙ Sheaf.sectionsFunctor J X) a b }

include hcomm in
/-- The inverse image of a sheaf of commutative rings along a finite-product-preserving
functor of sheaves of sets, as a presheaf of commutative rings. Its underlying presheaf of
rings is the inverse-image presheaf of rings of Stacks 03D2. -/
noncomputable def inverseImageCommRingPresheaf : Cᵒᵖ ⥤ CommRingCat.{w} where
  obj X :=
    letI := inverseImageSectionsCommRing J Φ O hcomm X
    CommRingCat.of ((Φ ⋙ Sheaf.sectionsFunctor J X).obj (Sheaf.ringSheaf O))
  map {X Y} g :=
    letI := inverseImageSectionsCommRing J Φ O hcomm X
    letI := inverseImageSectionsCommRing J Φ O hcomm Y
    CommRingCat.ofHom
      (Sheaf.ringObjHom O (Functor.whiskerLeft Φ (Sheaf.sectionsRestrict g)))
  map_id X := by
    refine CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_)
    change (Φ.obj (Sheaf.ringSheaf O)).obj.map (𝟙 X) x = x
    exact (Φ.obj (Sheaf.ringSheaf O)).obj.map_id_apply X x
  map_comp {X Y Z} g h := by
    refine CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_)
    change (Φ.obj (Sheaf.ringSheaf O)).obj.map (g ≫ h) x =
      (Φ.obj (Sheaf.ringSheaf O)).obj.map h ((Φ.obj (Sheaf.ringSheaf O)).obj.map g x)
    exact (Φ.obj (Sheaf.ringSheaf O)).obj.map_comp_apply g h x

include hcomm in
omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- Forgetting commutativity in the inverse image of a sheaf of commutative rings gives the
inverse-image presheaf of rings on the nose. -/
lemma ringPresheaf_inverseImageCommRingPresheaf :
    Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf (inverseImageCommRingPresheaf J Φ O hcomm) =
      pullbackRingPresheaf J Φ O :=
  rfl

include hcomm in
omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- The inverse-image sheaf of rings, exhibited as the underlying sheaf of rings of a
presheaf of commutative rings. -/
lemma pullbackRingSheaf_eq_commRingSheaf :
    pullbackRingSheaf J Φ O =
      commRingSheaf J (inverseImageCommRingPresheaf J Φ O hcomm)
        (pullbackRingSheaf J Φ O).property :=
  rfl

end InverseImageCommRing

/-! ## Morphisms of ringed topoi, and pullback and pushforward of their modules -/

section RingedTopos

universe w w' v u v' u'

open CategoryTheory.Functor CategoryTheory.Sheaf AlgebraicGeometry
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

/-- The sections of the structure sheaf of a ringed topos commute. -/
lemma ringSheaf_mul_comm (X : RingedTopos.{v, u, w})
    [X.J.HasSheafCompose (forget RingCat.{w})] (Z : X.Cᵒᵖ)
    (a b : (Sheaf.sectionsFunctor X.J Z).obj
      (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    a * b = b * a :=
  mul_comm (G := ToType (X.O.obj.obj Z)) a b

/-- A *morphism of ringed topoi* `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)`: a morphism of the
underlying topoi together with the map of structure sheaves, recorded in both its
direct-image form `f♯ : O_D ⟶ f_*O_C` and its inverse-image form `f⁻¹O_D ⟶ O_C`, the two
being required to correspond under the adjunction `f⁻¹ ⊣ f_*`. -/
structure RingedToposHom (X : RingedTopos.{v, u, w}) (Y : RingedTopos.{v', u', w'})
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
    [X.J.HasSheafCompose (forget RingCat.{w})]
    [Y.J.HasSheafCompose (forget RingCat.{w'})] where
  /-- The underlying morphism of topoi. -/
  toToposHom : MorphismOfTopoi X.Topos Y.Topos
  /-- The direct-image form of the structure map, `O_D ⟶ f_*O_C`. -/
  fSharp : Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
    pushforwardRingSheaf toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  /-- The inverse-image form of the structure map, `f⁻¹O_D ⟶ O_C`. -/
  fSharpInverseImage :
    inverseImageRingSheaf toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⟶
      Stacks.SheafOfModules.Tensor.ringSheaf X.O
  /-- The two forms of the structure map are adjunct to one another. -/
  fSharp_adjunct :
    (sheafCompose Y.J (forget RingCat.{w'})).map fSharp =
      toToposHom.adj.homEquiv (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        ((sheafCompose X.J (forget RingCat.{w})).map fSharpInverseImage)

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  (f : RingedToposHom X Y)

/-- The inverse image of the structure sheaf of the target, as a presheaf of commutative
rings on the source site. -/
noncomputable abbrev inverseImageStructureCommRing : X.Cᵒᵖ ⥤ CommRingCat.{w} :=
  inverseImageCommRingPresheaf X.J f.toToposHom.inverseImage
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) (ringSheaf_mul_comm Y)

/-- The inverse-image form of the structure map, read as a morphism of presheaves of
commutative rings. -/
noncomputable def fSharpCommRing : inverseImageStructureCommRing f ⟶ X.O.obj where
  app Z :=
    letI := inverseImageSectionsCommRing X.J f.toToposHom.inverseImage
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) (ringSheaf_mul_comm Y) Z
    CommRingCat.ofHom (f.fSharpInverseImage.hom.app Z).hom
  naturality {Z Z'} g := by
    refine CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_)
    exact ConcreteCategory.congr_hom (f.fSharpInverseImage.hom.naturality g) x

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})] in
/-- The inverse-image form of the structure map is recovered from its commutative-ring
form. -/
lemma commRingSheafMap_fSharpCommRing :
    commRingSheafMap X.J (fSharpCommRing f)
        (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property =
      f.fSharpInverseImage :=
  rfl

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})] in
/-- The direct-image form of the structure map is the unit `O_D ⟶ f_*f⁻¹O_D` followed by the
direct image of the inverse-image form, on underlying sheaves of sets. -/
lemma fSharp_underlying :
    (sheafCompose Y.J (forget RingCat.{w'})).map f.fSharp =
      (sheafCompose Y.J (forget RingCat.{w'})).map
          (ringUnit f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ≫
        f.toToposHom.pushforward.map
          ((sheafCompose X.J (forget RingCat.{w})).map f.fSharpInverseImage) := by
  rw [f.fSharp_adjunct,
    ringSheafMap_ringUnit f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)]
  rfl

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})] in
/-- The direct-image form of the structure map, read on sections. -/
lemma fSharp_sections (Z : Y.Cᵒᵖ)
    (r : (Sheaf.sectionsFunctor Y.J Z).obj
      (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    (f.toToposHom.pushforward ⋙ Sheaf.sectionsFunctor Y.J Z).map
        ((sheafCompose X.J (forget RingCat.{w})).map f.fSharpInverseImage)
        ((Sheaf.sectionsFunctor Y.J Z).map
          ((sheafCompose Y.J (forget RingCat.{w'})).map
            (ringUnit f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) r) =
      (Sheaf.sectionsFunctor Y.J Z).map
        ((sheafCompose Y.J (forget RingCat.{w'})).map f.fSharp) r :=
  ((congrArg (fun m ↦ (Sheaf.sectionsFunctor Y.J Z).map m r)
    (fSharp_underlying f)).trans
      ((Sheaf.sectionsFunctor Y.J Z).map_comp_apply _ _ _)).symm

/-- **Stacks 03D6, part (1)**: the pushforward of a sheaf of `O_C`-modules along a morphism
of ringed topoi. As a sheaf of abelian groups it is the direct image `f_*F`
(`moduleSheaf_pushforwardModules`), and its scalar action is the restriction along the
direct-image form `f♯ : O_D ⟶ f_*O_C` of the structure map of the direct-image action of
Stacks 03D1 (`pushforwardModules_smul`). -/
@[stacks 03D6 "part (1)"]
noncomputable def pushforwardModules :
    SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤
      SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) :=
  SheafOfModules.restrictScalars f.fSharpInverseImage ⋙
    directImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)

/-- The underlying sheaf of sets of the pushforward of a sheaf of modules along a morphism of
ringed topoi is the direct image of the underlying sheaf of sets. -/
lemma moduleSheaf_pushforwardModules
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
        ((pushforwardModules f).obj F) =
      f.toToposHom.pushforward.obj
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) F) :=
  rfl

/-- The scalar action on the pushforward of a sheaf of modules along a morphism of ringed
topoi is the restriction, along the direct-image form `f♯ : O_D ⟶ f_*O_C` of the structure
map, of the direct-image action `f_*O_C × f_*F ⟶ f_*F` of Stacks 03D1. This is the module
structure prescribed by Stacks 03D6, part (1). -/
lemma pushforwardModules_smul (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (Z : Y.Cᵒᵖ)
    (r : (Sheaf.sectionsFunctor Y.J Z).obj
      (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (x : (Sheaf.sectionsFunctor Y.J Z).obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
        ((pushforwardModules f).obj F))) :
    r • x =
      Sheaf.moduleSMulObj (Stacks.SheafOfModules.Tensor.ringSheaf X.O) F
        (f.toToposHom.pushforward ⋙ Sheaf.sectionsFunctor Y.J Z)
        ((Sheaf.sectionsFunctor Y.J Z).map
          ((sheafCompose Y.J (forget RingCat.{w'})).map f.fSharp) r) x := by
  have h := moduleSMulObj_restrictScalars f.fSharpInverseImage F
    (f.toToposHom.pushforward ⋙ Sheaf.sectionsFunctor Y.J Z)
    ((Sheaf.sectionsFunctor Y.J Z).map
      ((sheafCompose Y.J (forget RingCat.{w'})).map
        (ringUnit f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) r) x
  change Sheaf.moduleSMulObj
      (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      ((SheafOfModules.restrictScalars f.fSharpInverseImage).obj F)
      (f.toToposHom.pushforward ⋙ Sheaf.sectionsFunctor Y.J Z)
      ((Sheaf.sectionsFunctor Y.J Z).map
        ((sheafCompose Y.J (forget RingCat.{w'})).map
          (ringUnit f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) r) x = _
  rw [h, fSharp_sections]

variable [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Extension of scalars along the inverse-image form of the structure map of a morphism of
ringed topoi. -/
noncomputable def extendScalarsFSharp :
    SheafOfModules.{w}
        (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⥤
      SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  extendScalars X.J (fSharpCommRing f)
    (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property

namespace RingedToposHom

/-- **Stacks 03CZ** along the inverse-image form `f♯ : f⁻¹O_D ⟶ O_C` of the structure map of a
morphism of ringed topoi: extension of scalars along `f♯` (`extendScalarsFSharp`) is left
adjoint to restriction of scalars along it. This is the second factor of the adjunction of
Stacks 03D7 below, and the one canonical name for it. -/
noncomputable abbrev extendRestrictScalarsFSharpAdjunction :=
  extendRestrictScalarsAdjunction X.J (fSharpCommRing f)
    (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property

/-- **Stacks 03D6, part (2)**: the pullback of a sheaf of `O_D`-modules along a morphism of
ringed topoi: `O_C ⊗_{f⁻¹O_D} f⁻¹G`, i.e. the inverse image of Stacks 03D2 followed by
extension of scalars along the inverse-image form of the structure map. -/
@[stacks 03D6 "part (2)",
  stacks 03D6 "part (2), for the two-field morphism of ringed topoi",
  ega "0 4.3.1" "Ψ* functor",
  sga "4 IV 13.2.2" "commutative O, left mod"]
noncomputable def pullbackModules :
    SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', w'} Y.O) ⥤
      SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} X.O) :=
  inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⋙
    extendScalarsFSharp f

end RingedToposHom

/-- **Stacks 03D7**, the ringed-topoi case: for a morphism of ringed topoi
`(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)`, pullback of sheaves of modules is left adjoint to
pushforward. The adjunction supplies the canonical bijection
`Hom_{O_C}(f^*G, F) = Hom_{O_D}(G, f_*F)`, naturally in both variables. -/
@[stacks 03D7 "ringed topoi"]
noncomputable def pullbackAdjPushforwardModules :
    f.pullbackModules ⊣ pushforwardModules f :=
  (inverseImageAdjDirectImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).comp
    (extendRestrictScalarsAdjunction X.J (fSharpCommRing f)
      (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property)

end RingedTopos

end Stacks.Sheaves.RingedToposModules
