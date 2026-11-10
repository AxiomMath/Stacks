module

public import StacksFrontier.AlgebraicGeometry.Simplicial.LocallyGivenSimplicialGluingVanishing
public import StacksFrontier.AlgebraicGeometry.Simplicial.LocallyGivenSimplicialGluing
public import StacksFrontier.AlgebraicGeometry.Simplicial.SemiRepresentableTransitionCoherence
public import
  StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedTransitionCompExact
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CartesianDerivedModuleOfModuleSystem

/-!
# The simplicial system of locally given derived objects

In Situation 0DC9 — a category `B`, a functor `u : B ⥤ C` into a ringed site, objects `E_U` of
`D(O_{u(U)})` and isomorphisms `ρ_a : E_U|_{u(V)} ⟶ E_V` satisfying the cocycle condition — let
`L` be a simplicial object of `SR(B)`, `K = u(L)` and `((C/K)_total, O)` the ringed site of
Remark 0D9W, `O = a⁻¹O_C`. Writing `L_n = {U_{n,i}}_{i ∈ I_n}`, the proof of Stacks 0DCA
assembles the `E_U` into a cartesian simplicial system of the derived category of modules
(Stacks 0D9N):

* `D(O_n) = ∏_{i ∈ I_n} D(O_{u(U_{n,i})})`, and `E_n` is the formal product of the
  `E_{U_{n,i}}`;
* this decomposition is compatible with the transitions: on the `i`-th summand, the derived
  pullback `Lf_φ^*` along the transition of `φ : [m] ⟶ [n]` is the restriction of the `α(i)`-th
  summand along `u(a_i)`, where `L(φ) = (α, (a_i)_i)`, and these identifications are compatible
  with composition, the compositor of derived pullbacks becoming the comparison of restrictions
  of Situation 0DC9;
* the formal products of the `ρ_{a_i}` are the transitions `E_φ : Lf_φ^* E_m ⟶ E_n`, and the
  cocycle condition for the `ρ_a` gives the cocycle condition for the `E_φ`.

## Main definitions

* `AlgebraicGeometry.RingedSite.LocallyGiven.summandPullbackIso`: on the `i`-th summand the
  pullback along `f_φ` is restriction of the `α(i)`-th summand along `u(a_i)`.
* `AlgebraicGeometry.RingedSite.LocallyGiven.summandDerivedPullbackIso`: the same for derived
  pullbacks.
* `AlgebraicGeometry.RingedSite.LocallyGiven.localSystem`: the simplicial system `(E_n, E_φ)`.
* `AlgebraicGeometry.RingedSite.LocallyGiven.SummandIdentification`: an identification of the
  summandwise restrictions of an object `E` of `D(O)` with the `E_{U_{n,i}}`, compatible with the
  `ρ_a` — the clause "restricting to `E_{U_{n,i}}` compatibly" of Stacks 0DCA.

## Main results

* `AlgebraicGeometry.RingedSite.LocallyGiven.summandPullbackIso_comp` and
  `AlgebraicGeometry.RingedSite.LocallyGiven.summandDerivedPullbackIso_comp`: compatibility of the
  summandwise identifications with composition, for sheaves of modules and on derived categories.
* `AlgebraicGeometry.RingedSite.LocallyGiven.localSystem_cartesian`: the system is cartesian.
* `AlgebraicGeometry.RingedSite.LocallyGiven.SummandIdentification.systemIso`: a summandwise
  identification of `E` is an identification of the simplicial system of `E` with
  `localSystem`, and conversely
  (`AlgebraicGeometry.RingedSite.LocallyGiven.SummandIdentification.ofSystemIso`).

## References

* [Stacks Project, Tag 0DCA](https://stacks.math.columbia.edu/tag/0DCA)
* [Stacks Project, Tag 0DC9](https://stacks.math.columbia.edu/tag/0DC9)
* [Stacks Project, Tag 0D9N](https://stacks.math.columbia.edu/tag/0D9N)
* [Stacks Project, Tag 09WK](https://stacks.math.columbia.edu/tag/09WK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CategoryTheory.SimplicialSemiRepresentable Stacks.CategoryTheory.Hypercovering

universe u uB vB

namespace SheafOfModules

variable {C : Type*} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

/-- A morphism of sheaves of modules *fixes sections* if it sends every section to itself, up
to the identification of the types of sections of its source and target. -/
def FixesSections {A B : SheafOfModules.{u} R} (f : A ⟶ B) : Prop :=
  ∀ (V : Cᵒᵖ) (x : A.val.obj V), HEq ((f.val.app V).hom x) x

/-- A composite of morphisms fixing sections fixes sections. -/
theorem FixesSections.comp {A B D : SheafOfModules.{u} R} {f : A ⟶ B} {g : B ⟶ D}
    (hf : FixesSections f) (hg : FixesSections g) : FixesSections (f ≫ g) :=
  fun V x => (hg V ((f.val.app V).hom x)).trans (hf V x)

/-- Two morphisms fixing sections are equal. -/
theorem FixesSections.ext {A B : SheafOfModules.{u} R} {f g : A ⟶ B} (hf : FixesSections f)
    (hg : FixesSections g) : f = g :=
  SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V =>
    ModuleCat.hom_ext (LinearMap.ext fun x => eq_of_heq ((hf V x).trans (hg V x).symm)))

/-- The inverse of an isomorphism fixing sections fixes sections. -/
theorem FixesSections.inv {A B : SheafOfModules.{u} R} (f : A ≅ B) (hf : FixesSections f.hom) :
    FixesSections f.inv := fun V x => by
  have h := hf V ((f.inv.val.app V).hom x)
  have e : (f.hom.val.app V).hom ((f.inv.val.app V).hom x) = x := by
    rw [← ModuleCat.comp_apply, ← PresheafOfModules.comp_app, ← SheafOfModules.comp_val,
      Iso.inv_hom_id]
    rfl
  rw [e] at h
  exact h.symm

end SheafOfModules

namespace CategoryTheory

/-- A diagram chase: the shape in which the compositor of pullbacks is compared summandwise with
the comparison of restrictions. -/
theorem comp_chase {C D E : Type*} [Category C] [Category D] [Category E] (Sn : C ⥤ D)
    (Ov : E ⥤ D) {A B B' A₁ A₂ A₃ : C} {Y Z : D} {V₁ V₂ V₃ : E}
    (cPinv : A ⟶ B) (l₃ : B ⟶ B') (σ₃ : Sn.obj B' ⟶ Y) (tr : Y ⟶ Z)
    (Pl : A ⟶ A₁) (lR : A₁ ⟶ A₂) (cL : A₂ ⟶ B') (lP : A ⟶ A₃) (Rl : A₃ ⟶ A₂)
    (σP : Sn.obj A₃ ⟶ Ov.obj V₁) (Sl : V₁ ⟶ V₂) (σR : Sn.obj A₂ ⟶ Ov.obj V₂) (σψ : V₂ ⟶ V₃)
    (rinv : Ov.obj V₃ ⟶ Z)
    (hcomp : cPinv ≫ l₃ = Pl ≫ lR ≫ cL) (nl : Pl ≫ lR = lP ≫ Rl)
    (ns : Sn.map Rl ≫ σR = σP ≫ Ov.map Sl)
    (key : Sn.map cL ≫ σ₃ ≫ tr = σR ≫ Ov.map σψ ≫ rinv) :
    Sn.map cPinv ≫ (Sn.map l₃ ≫ σ₃) ≫ tr = (Sn.map lP ≫ σP) ≫ Ov.map (Sl ≫ σψ) ≫ rinv := by
  rw [Category.assoc, ← Sn.map_comp_assoc, hcomp, ← Category.assoc Pl, nl, Category.assoc,
    Sn.map_comp, Sn.map_comp, Category.assoc, Category.assoc, key, ← Category.assoc (Sn.map Rl),
    ns, Ov.map_comp]
  simp only [Category.assoc]

/-- A diagram chase removing identities. -/
theorem comp_id_chase {C D : Type*} [Category C] [Category D] (F : D ⥤ C) {a b c d : C}
    {x y : D} (A : a ⟶ b) (B : b ⟶ c) (T T₀ : c ⟶ d) (B' : a ⟶ F.obj x) (Cψ : x ⟶ y)
    (R : F.obj y ⟶ d) (hT : T = T₀) (h : A ≫ B ≫ T₀ = B' ≫ F.map Cψ ≫ R) :
    (A ≫ B ≫ 𝟙 c) ≫ T = (B' ≫ 𝟙 (F.obj x)) ≫ F.map (Cψ ≫ 𝟙 y) ≫ R := by
  simp [hT, h]

/-- The diagram chase behind the cocycle condition of the system of locally given objects. -/
theorem cocycle_chase {𝒟n 𝒟m 𝒟l : Type*} [Category 𝒟n] [Category 𝒟m] [Category 𝒟l]
    (Ra : 𝒟m ⥤ 𝒟n) (Rb : 𝒟l ⥤ 𝒟m) (Rab : 𝒟l ⥤ 𝒟n) (rC : Rab ≅ Rb ⋙ Ra)
    {A B X₃ Y₃ Gn Fn A' : 𝒟n} {Mψ Em Gm : 𝒟m} {D Gl : 𝒟l}
    (c : A ⟶ B) (t₃ : B ⟶ X₃) (e₃ : X₃ ⟶ Y₃) (ρ₃ : Y₃ ⟶ Gn) (einv : Gn ⟶ Fn)
    (trE : X₃ ⟶ Rab.obj D) (εl : D ⟶ Gl) (ρab : Rab.obj Gl ⟶ Gn)
    (tφL : A ⟶ Ra.obj Mψ) (tψ : Mψ ⟶ Rb.obj D)
    (d : A ⟶ A') (tφm : A' ⟶ Ra.obj Em) (εm : Em ≅ Gm) (ρa : Ra.obj Gm ⟶ Gn)
    (g : Mψ ⟶ Em) (ρb : Rb.obj Gl ≅ Gm)
    (htr : e₃ ≫ ρ₃ = trE ≫ Rab.map εl ≫ ρab)
    (kc : c ≫ t₃ ≫ trE = tφL ≫ Ra.map tψ ≫ rC.inv.app D)
    (nτ : d ≫ tφm = tφL ≫ Ra.map g)
    (mψ : g = tψ ≫ Rb.map εl ≫ ρb.hom ≫ εm.inv)
    (coc : ρab = rC.hom.app Gl ≫ Ra.map ρb.hom ≫ ρa)
    (nrc : Ra.map (Rb.map εl) ≫ rC.inv.app Gl = rC.inv.app D ≫ Rab.map εl) :
    c ≫ t₃ ≫ e₃ ≫ ρ₃ ≫ einv = d ≫ tφm ≫ Ra.map εm.hom ≫ ρa ≫ einv := by
  rw [reassoc_of% htr, reassoc_of% kc, reassoc_of% nτ, mψ, coc, ← reassoc_of% nrc]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Functor.map_comp, Functor.comp_obj]
  rw [← Ra.map_comp_assoc εm.inv εm.hom, Iso.inv_hom_id, Functor.map_id, Category.id_comp]

/-- The diagram chase turning an identification of systems into a summandwise identification. -/
theorem summand_chase {𝒞m 𝒞n 𝒟n 𝒟m : Type*} [Category 𝒞m] [Category 𝒞n] [Category 𝒟n]
    [Category 𝒟m] (Lf : 𝒞m ⥤ 𝒞n) (Sn : 𝒞n ⥤ 𝒟n) (Sm : 𝒞m ⥤ 𝒟m) (R : 𝒟m ⥤ 𝒟n)
    (τ : Lf ⋙ Sn ⟶ Sm ⋙ R) {A A' : 𝒞m} {B B' : 𝒞n} (s : Lf.obj A ⟶ B) (t : Lf.obj A' ⟶ B')
    (em : A ≅ A') (en : B ≅ B') (h : s ≫ en.hom = Lf.map em.hom ≫ t) {Gm : 𝒟m} {Gn : 𝒟n}
    (εm : Sm.obj A' ≅ Gm) (εn : Sn.obj B' ≅ Gn) (ρ : R.obj Gm ⟶ Gn)
    (ht : Sn.map t = τ.app A' ≫ R.map εm.hom ≫ ρ ≫ εn.inv) :
    Sn.map s ≫ (Sn.mapIso en ≪≫ εn).hom = τ.app A ≫ R.map ((Sm.mapIso em ≪≫ εm).hom) ≫ ρ := by
  have hn := congrArg Sn.map h
  simp only [Functor.map_comp] at hn
  have nτ := τ.naturality em.hom
  simp only [Functor.comp_map] at nτ
  simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn, ht]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [reassoc_of% nτ]

/-- The diagram chase turning a summandwise identification into an identification of systems. -/
theorem system_chase {𝒞m 𝒞n 𝒟n 𝒟m : Type*} [Category 𝒞m] [Category 𝒞n] [Category 𝒟n]
    [Category 𝒟m] (Lf : 𝒞m ⥤ 𝒞n) (Sn : 𝒞n ⥤ 𝒟n) (Sm : 𝒞m ⥤ 𝒟m) (R : 𝒟m ⥤ 𝒟n)
    (τ : Lf ⋙ Sn ⟶ Sm ⋙ R) {A A' : 𝒞m} {B B' : 𝒞n} (s : Lf.obj A ⟶ B) (t : Lf.obj A' ⟶ B')
    {Gm : 𝒟m} {Gn : 𝒟n} (εm : Sm.obj A' ≅ Gm) (εn : Sn.obj B' ≅ Gn) (ρ : R.obj Gm ⟶ Gn)
    (σm : Sm.obj A ≅ Gm) (σn : Sn.obj B ≅ Gn) (em : A ⟶ A') (en : B ⟶ B')
    (hem : Sm.map em = σm.hom ≫ εm.inv) (hen : Sn.map en = σn.hom ≫ εn.inv)
    (ht : Sn.map t = τ.app A' ≫ R.map εm.hom ≫ ρ ≫ εn.inv)
    (hs : Sn.map s ≫ σn.hom = τ.app A ≫ R.map σm.hom ≫ ρ) :
    Sn.map s ≫ Sn.map en = Sn.map (Lf.map em) ≫ Sn.map t := by
  have nτ := τ.naturality em
  simp only [Functor.comp_map] at nτ
  rw [hen, ← Category.assoc, hs, ht, reassoc_of% nτ, hem]
  simp

end CategoryTheory

namespace CategoryTheory.SimplicialSemiRepresentable

variable (X : RingedSite.{u, u, u}) [X.J.toCoverage.HasPullbacks]
  (K : SimplicialObject (FormalCoproduct.{u} X.C))

/-- `summandTransitionRestrictionIso` fixes sections. -/
theorem summandTransitionRestrictionIso_hom_app_fixesSections {m n : SimplexCategory} (φ : m ⟶ n)
    (i : (K.obj (op n)).I) (M : SheafOfModules.{u} (componentRing X K m)) :
    SheafOfModules.FixesSections ((summandTransitionRestrictionIso X K φ i).hom.app M) :=
  fun _ _ => HEq.rfl

/-- Restriction to a summand preserves morphisms fixing sections. -/
theorem summandRestriction_map_fixesSections (n : SimplexCategory) (i : (K.obj (op n)).I)
    {A B : SheafOfModules.{u} (componentRing X K n)} {f : A ⟶ B}
    (hf : SheafOfModules.FixesSections f) :
    SheafOfModules.FixesSections ((summandRestriction X K n i).map f) :=
  fun _ x => hf _ x

omit [X.J.toCoverage.HasPullbacks] in
/-- Restriction of sheaves of modules along a morphism of the site is additive. -/
instance overMap_additive {U V : X.C} (a : V ⟶ U) :
    (SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a).Additive where
  map_add := rfl

omit [X.J.toCoverage.HasPullbacks] in
/-- Restriction along a morphism of the site preserves morphisms fixing sections. -/
theorem overMap_map_fixesSections {U V : X.C} (a : V ⟶ U)
    {A B : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)} {f : A ⟶ B}
    (hf : SheafOfModules.FixesSections f) :
    SheafOfModules.FixesSections
      ((SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a).map f) :=
  fun _ x => hf _ x

/-- `transitionRestrictionCompIso` fixes sections. -/
theorem transitionRestrictionCompIso_hom_app_fixesSections {l m n : SimplexCategory} (ψ : l ⟶ m)
    (φ : m ⟶ n) (M : SheafOfModules.{u} (componentRing X K l)) :
    SheafOfModules.FixesSections ((transitionRestrictionCompIso X K ψ φ).hom.app M) :=
  fun V x => transitionRestrictionCompIso_hom_app_heq X K ψ φ M V x

end CategoryTheory.SimplicialSemiRepresentable

/-! ### The restrictions of Situation 0DC9

The restriction functors and their comparison along a composite are
`AlgebraicGeometry.RingedSite.derivedOverMap` and
`AlgebraicGeometry.RingedSite.derivedOverMapComp`, at the arrows of the indexing category. -/

namespace Stacks.SheafOfModules

/-- A presheaf on `Over Y` sends a morphism of `Over Y` with identity underlying morphism to a
map that is the identity, up to the identification of the types of sections. -/
theorem heq_presheaf_map_of_left_eq_id {C : Type*} [Category C] {Y Z : C}
    (P : (Over Y)ᵒᵖ ⥤ Ab) {p q : Z ⟶ Y} (k : Over.mk p ⟶ Over.mk q) (hk : k.left = 𝟙 Z)
    (x : P.obj (op (Over.mk q))) :
    HEq ((P.map k.op).hom x) x := by
  obtain rfl : p = q := by simpa [hk] using (Over.w k).symm
  obtain rfl : k = 𝟙 _ := Over.OverMorphism.ext hk
  rw [op_id, CategoryTheory.Functor.map_id]
  rfl

end Stacks.SheafOfModules

namespace AlgebraicGeometry.RingedSite.LocallyGiven

attribute [local instance] LocallyGiven.category

variable {X : RingedSite.{u, u, u}} (G : LocallyGiven.{0, u, u, u, uB, vB} X)

/-- Restriction of sheaves of modules along `u(a)` is additive. -/
theorem restrictionAdditive {V U : G.B} (a : V ⟶ U) :
    (SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      (G.u.map a)).Additive :=
  overMap_additive _ _

/-- The comparison of the restrictions of sheaves of modules along `u(a)`, `u(b)` and
`u(b ≫ a)`. -/
abbrev restrictionCompOrdinary {W V U : G.B} (b : W ⟶ V) (a : V ⟶ U) :
    SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (G.u.map (b ≫ a)) ≅
      SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (G.u.map a) ⋙
        SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (G.u.map b) :=
  (overMapCompIsoOfEq.{0} X (G.u.map_comp b a).symm).symm

/-- `overMapCompIsoOfEq` fixes sections. -/
theorem overMapCompIsoOfEq_hom_app_fixesSections {U V W : X.C} {f : V ⟶ U} {g : W ⟶ V}
    {h : W ⟶ U} (e : g ≫ f = h)
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) :
    SheafOfModules.FixesSections ((overMapCompIsoOfEq.{0} X e).hom.app M) := by
  subst e
  intro T x
  exact Stacks.SheafOfModules.heq_presheaf_map_of_left_eq_id M.val.presheaf
    ((Over.mapComp g f).hom.app T.unop) rfl x

/-- **The comparison of restrictions along a composite is the identity on sections.** -/
theorem restrictionCompOrdinary_hom_app_fixesSections {W V U : G.B} (b : W ⟶ V) (a : V ⟶ U)
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (G.u.obj U))) :
    SheafOfModules.FixesSections ((G.restrictionCompOrdinary b a).hom.app M) :=
  SheafOfModules.FixesSections.inv ((overMapCompIsoOfEq.{0} X (G.u.map_comp b a).symm).app M)
    (overMapCompIsoOfEq_hom_app_fixesSections (G.u.map_comp b a).symm M)

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- Derived restriction along `u(a)`. -/
abbrev restriction {V U : G.B} (a : V ⟶ U) :
    LocalDerivedCategory.{0} X (G.u.obj U) ⥤ LocalDerivedCategory.{0} X (G.u.obj V) :=
  derivedOverMap.{0} X (G.u.map a)

/-- The comparison of derived restrictions along `u(a)`, `u(b)` and `u(b ≫ a)`. -/
abbrev restrictionComp {W V U : G.B} (b : W ⟶ V) (a : V ⟶ U) :
    G.restriction (b ≫ a) ≅ G.restriction a ⋙ G.restriction b :=
  derivedOverMapComp.{0} X (G.u.map_comp b a).symm

/-- Derived restriction along `u(a)` is induced by restriction of complexes. -/
abbrev restrictionFactors {V U : G.B} (a : V ⟶ U) :
    letI := G.restrictionAdditive a
    DerivedCategory.Q ⋙ G.restriction a ≅
      (SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        (G.u.map a)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  letI := G.restrictionAdditive a
  have := overMap_preservesFiniteLimits.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (G.u.map a)
  have := overMap_preservesFiniteColimits.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
    (G.u.map a)
  (SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
    (G.u.map a)).mapDerivedCategoryFactors

/-- **The derived comparison of restrictions is induced by the comparison of sheaves of
modules**, on the image of a complex. -/
theorem restrictionCompFactors {W V U : G.B} (b : W ⟶ V) (a : V ⟶ U)
    (C : HomologicalComplex
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (G.u.obj U)))
      (ComplexShape.up ℤ)) :
    letI := G.restrictionAdditive a
    letI := G.restrictionAdditive b
    letI := G.restrictionAdditive (b ≫ a)
    (G.restrictionComp b a).hom.app (DerivedCategory.Q.obj C) ≫
      (G.restriction b).map ((G.restrictionFactors a).hom.app C) ≫
      (G.restrictionFactors b).hom.app
        (((SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          (G.u.map a)).mapHomologicalComplex (ComplexShape.up ℤ)).obj C) ≫
      DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexCompIso
          (G.restrictionCompOrdinary b a).symm (ComplexShape.up ℤ)).hom.app C) =
      (G.restrictionFactors (b ≫ a)).hom.app C := by
  simp only [restrictionComp, derivedOverMapComp, Iso.symm_hom, Localization.liftNatIso_inv,
    Localization.liftNatTrans_app, Localization.Lifting.iso, Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_inv_app,
    Functor.associator_hom_app, Category.id_comp, Category.comp_id, Category.assoc,
    Iso.symm_inv, Iso.symm_symm_eq]
  simp only [restriction, restrictionFactors, derivedOverMap, Category.assoc]
  simp [← Functor.map_comp, ← Functor.map_comp_assoc]

end Derived

end AlgebraicGeometry.RingedSite.LocallyGiven

namespace AlgebraicGeometry.RingedSite.LocallyGiven

attribute [local instance] LocallyGiven.category

variable {X : RingedSite.{u, u, u}} [X.J.toCoverage.HasPullbacks]
  (G : LocallyGiven.{0, u, u, u, uB, vB} X) (L : SimplicialObject (FormalCoproduct.{u} G.B))

/-- Pullback of modules along the transition `f_φ` of `K = u(L)`. -/
abbrev transitionPullback {m n : SimplexCategory} (φ : m ⟶ n) :=
  ((situation X.J (G.image L)).transitionRingedToposHom (structureSheaf X (G.image L))
    φ).toModulesHom.pullbackModules

/-- Restriction of `O_n`-modules to the summand `C/u(U_{n,i})`, indexed by the summands of `L_n`.
It is `CategoryTheory.SimplicialSemiRepresentable.summandRestriction` for `K = u(L)`. -/
def summandRestrictionB (n : SimplexCategory) (i : (L.obj (op n)).I) :
    SheafOfModules.{u} (componentRing X (G.image L) n) ⥤
      SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over
        (G.u.obj ((L.obj (op n)).obj i))) :=
  summandRestriction X (G.image L) n i

/-- Restriction to a summand is additive. -/
instance summandRestrictionB_additive (n : SimplexCategory) (i : (L.obj (op n)).I) :
    (G.summandRestrictionB L n i).Additive :=
  summandRestriction_additive X (G.image L) n i

/-- Restriction to a summand is left exact. -/
instance summandRestrictionB_preservesFiniteLimits (n : SimplexCategory)
    (i : (L.obj (op n)).I) : PreservesFiniteLimits (G.summandRestrictionB L n i) :=
  summandRestriction_preservesFiniteLimits X (G.image L) n i

/-- Restriction to a summand is right exact. -/
instance summandRestrictionB_preservesFiniteColimits (n : SimplexCategory)
    (i : (L.obj (op n)).I) : PreservesFiniteColimits (G.summandRestrictionB L n i) :=
  summandRestriction_preservesFiniteColimits X (G.image L) n i

/-- Restriction to a summand preserves morphisms fixing sections. -/
theorem summandRestrictionB_map_fixesSections (n : SimplexCategory) (i : (L.obj (op n)).I)
    {A B : SheafOfModules.{u} (componentRing X (G.image L) n)} {f : A ⟶ B}
    (hf : SheafOfModules.FixesSections f) :
    SheafOfModules.FixesSections ((G.summandRestrictionB L n i).map f) :=
  summandRestriction_map_fixesSections X (G.image L) n i hf

/-- **On the `i`-th summand, the pullback along `f_φ` is restriction of the `α(i)`-th summand
along `u(a_i)`**, where `L(φ) = (α, (a_i)_i)`. -/
def summandPullbackIso {m n : SimplexCategory} (φ : m ⟶ n) (i : (L.obj (op n)).I) :
    G.transitionPullback L φ ⋙ G.summandRestrictionB L n i ≅
      G.summandRestrictionB L m ((L.map φ.op).f i) ⋙
        SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          (G.u.map ((L.map φ.op).φ i)) :=
  Functor.isoWhiskerRight (transitionPullbackModulesIso X (G.image L) φ) _ ≪≫
    summandTransitionRestrictionIso X (G.image L) φ i

omit [X.J.toCoverage.HasPullbacks] in
/-- The inverse comparison of restrictions along a composite is the identity on sections. -/
theorem restrictionCompOrdinary_inv_app_fixesSections {W V U : G.B} (b : W ⟶ V) (a : V ⟶ U)
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (G.u.obj U))) :
    SheafOfModules.FixesSections ((G.restrictionCompOrdinary b a).inv.app M) :=
  SheafOfModules.FixesSections.inv ((G.restrictionCompOrdinary b a).app M)
    (G.restrictionCompOrdinary_hom_app_fixesSections b a M)

/-- The functor `C/K_l`-modules `⥤` `C/u(U_{n,i})`-modules attached to a morphism
`k : L_n ⟶ L_l` of `SR(B)` and a summand `i`: restriction to the summand `k(i)`, then along
`u(k_i)`. -/
abbrev summandRestrictionAlong {n l : SimplexCategory} (k : L.obj (op n) ⟶ L.obj (op l))
    (i : (L.obj (op n)).I) :=
  G.summandRestrictionB L l (k.f i) ⋙
    SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (G.u.map (k.φ i))

/-- The `eqToHom` between the restrictions along equal morphisms of `SR(B)` fixes sections. -/
theorem eqToHom_summandRestrictionAlong_fixesSections {n l : SimplexCategory}
    {k k' : L.obj (op n) ⟶ L.obj (op l)} (h : k = k') (i : (L.obj (op n)).I)
    (M : SheafOfModules.{u} (componentRing X (G.image L) l)) :
    SheafOfModules.FixesSections ((eqToHom (congrArg (fun k => G.summandRestrictionAlong L k i)
      h)).app M) := by
  subst h
  exact fun _ _ => HEq.rfl

/-- The summandwise identifications of the transition restrictions are compatible with
composition. -/
theorem summandTransitionRestrictionIso_comp {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (i : (L.obj (op n)).I) (M : SheafOfModules.{u} (componentRing X (G.image L) l)) :
    (G.summandRestrictionB L n i).map
        ((transitionRestrictionCompIso X (G.image L) ψ φ).hom.app M) ≫
      (summandTransitionRestrictionIso X (G.image L) (ψ ≫ φ) i).hom.app M ≫
        (eqToHom (congrArg (fun k => G.summandRestrictionAlong L k i)
          (L.map_comp φ.op ψ.op))).app M =
      (summandTransitionRestrictionIso X (G.image L) φ i).hom.app
          ((transitionRestriction X (G.image L) ψ).obj M) ≫
        (SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
            (G.u.map ((L.map φ.op).φ i))).map
          ((summandTransitionRestrictionIso X (G.image L) ψ ((L.map φ.op).f i)).hom.app M) ≫
          (G.restrictionCompOrdinary ((L.map φ.op).φ i)
            ((L.map ψ.op).φ ((L.map φ.op).f i))).inv.app
            ((G.summandRestrictionB L l ((L.map ψ.op).f ((L.map φ.op).f i))).obj M) := by
  refine SheafOfModules.FixesSections.ext ?_ ?_
  · exact (G.summandRestrictionB_map_fixesSections L n i
      (transitionRestrictionCompIso_hom_app_fixesSections X _ ψ φ M)).comp
        ((summandTransitionRestrictionIso_hom_app_fixesSections X _ (ψ ≫ φ) i M).comp
          (G.eqToHom_summandRestrictionAlong_fixesSections L (L.map_comp φ.op ψ.op) i M))
  · exact (summandTransitionRestrictionIso_hom_app_fixesSections X (G.image L) φ i
      ((transitionRestriction X (G.image L) ψ).obj M)).comp
      ((overMap_map_fixesSections X (G.u.map ((L.map φ.op).φ i))
          (summandTransitionRestrictionIso_hom_app_fixesSections X (G.image L) ψ
            ((L.map φ.op).f i) M)).comp
        (G.restrictionCompOrdinary_inv_app_fixesSections ((L.map φ.op).φ i)
          ((L.map ψ.op).φ ((L.map φ.op).f i))
          ((G.summandRestrictionB L l ((L.map ψ.op).f ((L.map φ.op).f i))).obj M)))

/-- The components of `summandPullbackIso`. -/
theorem summandPullbackIso_hom_app {m n : SimplexCategory} (φ : m ⟶ n) (i : (L.obj (op n)).I)
    (M : SheafOfModules.{u} (componentRing X (G.image L) m)) :
    (G.summandPullbackIso L φ i).hom.app M =
      (G.summandRestrictionB L n i).map
          ((transitionPullbackModulesIso X (G.image L) φ).hom.app M) ≫
        (summandTransitionRestrictionIso X (G.image L) φ i).hom.app M :=
  rfl

/-- **The summandwise identifications of the pullbacks are compatible with composition.** For
composable `ψ : l ⟶ m`, `φ : m ⟶ n` and a summand `i` of `L_n`, with `L(φ)` sending `i` to `j`
along `a` and `L(ψ)` sending `j` to `j'` along `b`, the compositor of pullbacks of Stacks 09WE,
read on the `i`-th summand through `summandPullbackIso`, is the comparison
`G.restrictionCompOrdinary a b` of the restrictions along `u(a)` and `u(b)`. -/
theorem summandPullbackIso_comp {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (i : (L.obj (op n)).I) (M : SheafOfModules.{u} (componentRing X (G.image L) l)) :
    (G.summandRestrictionB L n i).map
        (((situation X.J (G.image L)).transitionPullbackModulesCompIso
          (structureSheaf X (G.image L)) ψ φ).inv.app M) ≫
      (G.summandPullbackIso L (ψ ≫ φ) i).hom.app M ≫
        (eqToHom (congrArg (fun k => G.summandRestrictionAlong L k i)
          (L.map_comp φ.op ψ.op))).app M =
      (G.summandPullbackIso L φ i).hom.app ((G.transitionPullback L ψ).obj M) ≫
        (SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
            (G.u.map ((L.map φ.op).φ i))).map
          ((G.summandPullbackIso L ψ ((L.map φ.op).f i)).hom.app M) ≫
          (G.restrictionCompOrdinary ((L.map φ.op).φ i)
            ((L.map ψ.op).φ ((L.map φ.op).f i))).inv.app
            ((G.summandRestrictionB L l ((L.map ψ.op).f ((L.map φ.op).f i))).obj M) := by
  have hcomp := transitionPullbackModulesCompIso_comm X (G.image L) ψ φ M
  have nl := (transitionPullbackModulesIso X (G.image L) φ).hom.naturality
    ((transitionPullbackModulesIso X (G.image L) ψ).hom.app M)
  have ns := (summandTransitionRestrictionIso X (G.image L) φ i).hom.naturality
    ((transitionPullbackModulesIso X (G.image L) ψ).hom.app M)
  have key := G.summandTransitionRestrictionIso_comp L ψ φ i M
  rw [G.summandPullbackIso_hom_app, G.summandPullbackIso_hom_app, G.summandPullbackIso_hom_app]
  exact comp_chase (G.summandRestrictionB L n i)
    (SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      (G.u.map ((L.map φ.op).φ i)))
    (((situation X.J (G.image L)).transitionPullbackModulesCompIso
      (structureSheaf X (G.image L)) ψ φ).inv.app M)
    ((transitionPullbackModulesIso X (G.image L) (ψ ≫ φ)).hom.app M)
    ((summandTransitionRestrictionIso X (G.image L) (ψ ≫ φ) i).hom.app M)
    ((eqToHom (congrArg (fun k => G.summandRestrictionAlong L k i)
      (L.map_comp φ.op ψ.op))).app M)
    ((G.transitionPullback L φ).map ((transitionPullbackModulesIso X (G.image L) ψ).hom.app M))
    ((transitionPullbackModulesIso X (G.image L) φ).hom.app
      ((transitionRestriction X (G.image L) ψ).obj M))
    ((transitionRestrictionCompIso X (G.image L) ψ φ).hom.app M)
    ((transitionPullbackModulesIso X (G.image L) φ).hom.app ((G.transitionPullback L ψ).obj M))
    ((transitionRestriction X (G.image L) φ).map
      ((transitionPullbackModulesIso X (G.image L) ψ).hom.app M))
    ((summandTransitionRestrictionIso X (G.image L) φ i).hom.app
      ((G.transitionPullback L ψ).obj M))
    ((G.summandRestrictionB L m ((L.map φ.op).f i)).map
      ((transitionPullbackModulesIso X (G.image L) ψ).hom.app M))
    ((summandTransitionRestrictionIso X (G.image L) φ i).hom.app
      ((transitionRestriction X (G.image L) ψ).obj M))
    ((summandTransitionRestrictionIso X (G.image L) ψ ((L.map φ.op).f i)).hom.app M)
    ((G.restrictionCompOrdinary ((L.map φ.op).φ i)
      ((L.map ψ.op).φ ((L.map φ.op).f i))).inv.app
      ((G.summandRestrictionB L l ((L.map ψ.op).f ((L.map φ.op).f i))).obj M))
    hcomp nl ns key

/-! ### The derived summandwise identifications -/

section Derived

attribute [local instance] HasDerivedCategory.standard
  CategoryTheory.SimplicialSiteSituation.hasWeakSheafifyComponent

/-- The functor on cochain complexes realizing `summandDerivedRestrictionAlong`. -/
abbrev summandRestrictionAlongComplexes {n l : SimplexCategory} (k : L.obj (op n) ⟶ L.obj (op l))
    (i : (L.obj (op n)).I) :=
  (G.summandRestrictionB L l (k.f i)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    (SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      (G.u.map (k.φ i))).mapHomologicalComplex (ComplexShape.up ℤ)

/-- `summandPullbackIso` acting on cochain complexes. -/
def summandPullbackComplexesIso {m n : SimplexCategory} (φ : m ⟶ n) (i : (L.obj (op n)).I) :
    (G.transitionPullback L φ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (G.summandRestrictionB L n i).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      G.summandRestrictionAlongComplexes L (L.map φ.op) i :=
  NatIso.mapHomologicalComplex (G.summandPullbackIso L φ i) (ComplexShape.up ℤ)

/-- The degreewise components of `summandPullbackComplexesIso`. -/
theorem summandPullbackComplexesIso_hom_app_f {m n : SimplexCategory} (φ : m ⟶ n)
    (i : (L.obj (op n)).I)
    (C : CochainComplex (SheafOfModules.{u} (componentRing X (G.image L) m)) ℤ) (p : ℤ) :
    ((G.summandPullbackComplexesIso L φ i).hom.app C).f p =
      (G.summandPullbackIso L φ i).hom.app (C.X p) :=
  rfl

/-- **On the `i`-th summand, the derived pullback along `f_φ` is the derived restriction of the
`α(i)`-th summand along `a_i`**: the identification `summandPullbackIso` lifted along the
localizations of cochain complexes. -/
def summandDerivedPullbackIso {m n : SimplexCategory} (φ : m ⟶ n) (i : (L.obj (op n)).I) :
    (situation X.J (G.image L)).derivedTransitionPullback (structureSheaf X (G.image L)) φ ⋙
        (G.summandRestrictionB L n i).mapDerivedCategory ≅
      (G.summandRestrictionB L m ((L.map φ.op).f i)).mapDerivedCategory ⋙
        G.restriction ((L.map φ.op).φ i) :=
  letI := (situation X.J (G.image L)).transitionPullbackModules_preservesFiniteLimits
    (structureSheaf X (G.image L)) φ (transitionRingedToposHom_isFlat X (G.image L) φ)
  NatIso.liftAlong (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
    (Functor.compFactorization ((situation X.J (G.image L)).derivedTransitionPullbackFactors
        (structureSheaf X (G.image L)) φ (transitionRingedToposHom_isFlat X (G.image L) φ))
      (G.summandRestrictionB L n i).mapDerivedCategoryFactors)
    (Functor.compFactorization
      (G.summandRestrictionB L m ((L.map φ.op).f i)).mapDerivedCategoryFactors
      (G.restrictionFactors ((L.map φ.op).φ i)))
    (G.summandPullbackComplexesIso L φ i)

omit [X.J.toCoverage.HasPullbacks] in
/-- **The comparison of derived restrictions of Situation 0DC9 is induced degreewise** by the
comparison of restrictions of sheaves of modules. -/
theorem restrictionComp_inv_isInducedBy {W V U : G.B} (b : W ⟶ V) (a : V ⟶ U) :
    letI := G.restrictionAdditive a
    letI := G.restrictionAdditive b
    letI := G.restrictionAdditive (b ≫ a)
    NatTrans.IsInducedBy
      (Functor.compFactorization (G.restrictionFactors a) (G.restrictionFactors b))
      (G.restrictionFactors (b ≫ a)) (G.restrictionComp b a).inv
      (Functor.mapHomologicalComplexCompIso (G.restrictionCompOrdinary b a).symm
        (ComplexShape.up ℤ)).hom := by
  let := G.restrictionAdditive a
  let := G.restrictionAdditive b
  let := G.restrictionAdditive (b ≫ a)
  refine NatTrans.IsInducedBy.inv (γ := G.restrictionComp b a)
    (γ₀ := (Functor.mapHomologicalComplexCompIso (G.restrictionCompOrdinary b a).symm
      (ComplexShape.up ℤ)).symm) fun C => ?_
  have h := G.restrictionCompFactors b a C
  simp only [Functor.compFactorization_hom_app] at h ⊢
  rw [← h]
  simp

/-- Derived restriction to the summand `k(i)` of `L_l`, followed by the derived restriction of
Situation 0DC9 along `k_i`, for a morphism `k : L_n ⟶ L_l` of `SR(B)`. -/
abbrev summandDerivedRestrictionAlong {n l : SimplexCategory} (k : L.obj (op n) ⟶ L.obj (op l))
    (i : (L.obj (op n)).I) :=
  (G.summandRestrictionB L l (k.f i)).mapDerivedCategory ⋙ G.restriction (k.φ i)

/-- The factorization of `summandDerivedRestrictionAlong` through the localization of cochain
complexes. -/
abbrev summandDerivedRestrictionAlongFactors {n l : SimplexCategory}
    (k : L.obj (op n) ⟶ L.obj (op l)) (i : (L.obj (op n)).I) :=
  Functor.compFactorization (G.summandRestrictionB L l (k.f i)).mapDerivedCategoryFactors
    (G.restrictionFactors (k.φ i))

/-- The `eqToHom` between the derived restrictions along equal morphisms of `SR(B)` is induced
by the `eqToHom` on cochain complexes. -/
theorem eqToHom_summandDerivedRestrictionAlong_isInducedBy {n l : SimplexCategory}
    {k k' : L.obj (op n) ⟶ L.obj (op l)} (h : k = k') (i : (L.obj (op n)).I) :
    NatTrans.IsInducedBy (L₁ := DerivedCategory.Q) (L₂ := DerivedCategory.Q)
      (X₀ := G.summandRestrictionAlongComplexes L k i)
      (Y₀ := G.summandRestrictionAlongComplexes L k' i)
      (G.summandDerivedRestrictionAlongFactors L k i)
      (G.summandDerivedRestrictionAlongFactors L k' i)
      (eqToHom (congrArg (fun k => G.summandDerivedRestrictionAlong L k i) h))
      (eqToHom (congrArg (fun k => G.summandRestrictionAlongComplexes L k i) h)) := by
  subst h
  exact NatTrans.IsInducedBy.id

/-- The degreewise components of the `eqToHom` between the restrictions of cochain complexes
along equal morphisms of `SR(B)`. -/
theorem eqToHom_summandRestrictionAlongComplexes_app_f {n l : SimplexCategory}
    {k k' : L.obj (op n) ⟶ L.obj (op l)} (h : k = k') (i : (L.obj (op n)).I)
    (C : CochainComplex (SheafOfModules.{u} (componentRing X (G.image L) l)) ℤ) (p : ℤ) :
    ((eqToHom (congrArg (fun k => G.summandRestrictionAlongComplexes L k i) h)).app C).f p =
      (eqToHom (congrArg (fun k => G.summandRestrictionAlong L k i) h)).app (C.X p) := by
  subst h
  rfl

/-- `summandDerivedPullbackIso` is induced by `summandPullbackComplexesIso`. -/
theorem summandDerivedPullbackIso_hom_isInducedBy {m n : SimplexCategory} (φ : m ⟶ n)
    (i : (L.obj (op n)).I) :
    letI := (situation X.J (G.image L)).transitionPullbackModules_preservesFiniteLimits
      (structureSheaf X (G.image L)) φ (transitionRingedToposHom_isFlat X (G.image L) φ)
    NatTrans.IsInducedBy
      (Functor.compFactorization ((situation X.J (G.image L)).derivedTransitionPullbackFactors
          (structureSheaf X (G.image L)) φ (transitionRingedToposHom_isFlat X (G.image L) φ))
        (G.summandRestrictionB L n i).mapDerivedCategoryFactors)
      (Functor.compFactorization
        (G.summandRestrictionB L m ((L.map φ.op).f i)).mapDerivedCategoryFactors
        (G.restrictionFactors ((L.map φ.op).φ i)))
      (G.summandDerivedPullbackIso L φ i).hom
      (G.summandPullbackComplexesIso L φ i).hom :=
  NatTrans.isInducedBy_liftAlong _ _ _ _

/-- The degreewise form of `summandDerivedPullbackIso_comp`. -/
theorem summandPullbackComplexesIso_comp {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (i : (L.obj (op n)).I) :
    (Functor.whiskerRight (Functor.mapHomologicalComplexCompIso
        ((situation X.J (G.image L)).transitionPullbackModulesCompIso
          (structureSheaf X (G.image L)) ψ φ).symm (ComplexShape.up ℤ)).hom
        ((G.summandRestrictionB L n i).mapHomologicalComplex (ComplexShape.up ℤ)) ≫
      (G.summandPullbackComplexesIso L (ψ ≫ φ) i).hom) ≫
        eqToHom (congrArg (fun k => G.summandRestrictionAlongComplexes L k i)
          (L.map_comp φ.op ψ.op)) =
      (Functor.associator _ _ _).hom ≫
        ((Functor.whiskerLeft ((G.transitionPullback L ψ).mapHomologicalComplex (ComplexShape.up ℤ))
            (G.summandPullbackComplexesIso L φ i).hom ≫ (Functor.associator _ _ _).inv) ≫
          (Functor.whiskerRight (G.summandPullbackComplexesIso L ψ ((L.map φ.op).f i)).hom
              ((SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
                (G.u.map ((L.map φ.op).φ i))).mapHomologicalComplex (ComplexShape.up ℤ)) ≫
            ((Functor.associator _ _ _).hom ≫
              Functor.whiskerLeft ((G.summandRestrictionB L l
                  ((L.map ψ.op).f ((L.map φ.op).f i))).mapHomologicalComplex (ComplexShape.up ℤ))
                (Functor.mapHomologicalComplexCompIso (G.restrictionCompOrdinary ((L.map φ.op).φ i)
                  ((L.map ψ.op).φ ((L.map φ.op).f i))).symm (ComplexShape.up ℤ)).hom))) := by
  refine NatTrans.ext (funext fun C => HomologicalComplex.hom_ext _ _ fun p => ?_)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    HomologicalComplex.comp_f, Iso.symm_hom, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id,
    Functor.mapHomologicalComplexCompIso_hom_app_f,
    Functor.mapHomologicalComplex_map_f, summandPullbackComplexesIso_hom_app_f,
    Functor.mapHomologicalComplex_obj_X]
  rw [G.eqToHom_summandRestrictionAlongComplexes_app_f L (L.map_comp φ.op ψ.op) i C p,
    Category.assoc]
  have h := G.summandPullbackIso_comp L ψ φ i (C.X p)
  convert h using 2

/-- **The derived summandwise identifications are compatible with composition**: under them,
the composition comparison `Lf_ψ^* ⋙ Lf_φ^* ⟶ Lf_{ψ ≫ φ}^*` of derived pullbacks is, on the
`i`-th summand, the comparison `G.restrictionComp a b` of Situation 0DC9. -/
theorem summandDerivedPullbackIso_comp {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (i : (L.obj (op n)).I) :
    Functor.whiskerRight ((situation X.J (G.image L)).derivedTransitionCompComparison
        (structureSheaf X (G.image L)) ψ φ) (G.summandRestrictionB L n i).mapDerivedCategory ≫
      (G.summandDerivedPullbackIso L (ψ ≫ φ) i).hom ≫
        eqToHom (congrArg (fun k => G.summandDerivedRestrictionAlong L k i)
          (L.map_comp φ.op ψ.op)) =
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft ((situation X.J (G.image L)).derivedTransitionPullback
          (structureSheaf X (G.image L)) ψ) (G.summandDerivedPullbackIso L φ i).hom ≫
          (Functor.associator _ _ _).inv ≫
            Functor.whiskerRight (G.summandDerivedPullbackIso L ψ ((L.map φ.op).f i)).hom
              (G.restriction ((L.map φ.op).φ i)) ≫
              (Functor.associator _ _ _).hom ≫
                Functor.whiskerLeft (G.summandRestrictionB L l
                    ((L.map ψ.op).f ((L.map φ.op).f i))).mapDerivedCategory
                  (G.restrictionComp ((L.map φ.op).φ i)
                    ((L.map ψ.op).φ ((L.map φ.op).f i))).inv := by
  have hfl := fun {a b : SimplexCategory} (χ : a ⟶ b) =>
    transitionRingedToposHom_isFlat X (G.image L) χ
  let := fun {a b : SimplexCategory} (χ : a ⟶ b) =>
    (situation X.J (G.image L)).transitionPullbackModules_preservesFiniteLimits
      (structureSheaf X (G.image L)) χ (hfl χ)
  have hC1 := (situation X.J (G.image L)).derivedTransitionCompComparison_isInducedBy
    (structureSheaf X (G.image L)) ψ φ (hfl ψ) (hfl φ) (hfl (ψ ≫ φ))
  have hL := ((hC1.whiskerRight (G.summandRestrictionB L n i).mapDerivedCategoryFactors).comp
    (G.summandDerivedPullbackIso_hom_isInducedBy L (ψ ≫ φ) i)).comp
      (G.eqToHom_summandDerivedRestrictionAlong_isInducedBy L (L.map_comp φ.op ψ.op) i)
  have hR := (NatTrans.IsInducedBy.associator _ _ _).comp
    (((NatTrans.IsInducedBy.whiskerLeft _ (G.summandDerivedPullbackIso_hom_isInducedBy L φ i)).comp
      (NatTrans.IsInducedBy.associator_inv _ _ _)).comp
      (((G.summandDerivedPullbackIso_hom_isInducedBy L ψ ((L.map φ.op).f i)).whiskerRight
        (G.restrictionFactors ((L.map φ.op).φ i))).comp
        ((NatTrans.IsInducedBy.associator _ _ _).comp
          (NatTrans.IsInducedBy.whiskerLeft _ (G.restrictionComp_inv_isInducedBy
            ((L.map φ.op).φ i) ((L.map ψ.op).φ ((L.map φ.op).f i)))))))
  have key := NatTrans.IsInducedBy.ext_of_eq (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
    hL hR
  refine Eq.trans (Category.assoc _ _ _).symm (Eq.trans (key ?_) (by simp only [Category.assoc]))
  exact G.summandPullbackComplexesIso_comp L ψ φ i

/-! ### The simplicial system -/

/-- The summand restrictions identify `Mod(O_n)` with `∏_i Mod(O_{u(U_{n,i})})` (Stacks
0D9U). -/
instance isEquivalence_pi'_summandRestrictionB (n : SimplexCategory) :
    (Functor.pi' (G.summandRestrictionB L n)).IsEquivalence :=
  isEquivalence_pi'_summandRestriction X (G.image L) n

/-- The derived restriction to the summand `C/u(U_{n,i})` of the degree-`n` component. -/
abbrev summandDerivedRestriction (n : SimplexCategory) (i : (L.obj (op n)).I) :=
  (G.summandRestrictionB L n i).mapDerivedCategory

/-- **The object `E_n` of `D(O_n)`** of the proof of Stacks 0DCA: the formal product of the
locally given objects `E_{U_{n,i}}`, along `D(O_n) = ∏_i D(O_{u(U_{n,i})})`. -/
def systemObj (n : SimplexCategory) :
    DerivedCategory (SheafOfModules.{u} (componentRing X (G.image L) n)) :=
  (Functor.pi' (G.summandDerivedRestriction L n)).objPreimage
    (fun i => G.obj ((L.obj (op n)).obj i))

/-- The restriction of `E_n` to the summand `C/u(U_{n,i})` is `E_{U_{n,i}}`. -/
def systemObjIso (n : SimplexCategory) (i : (L.obj (op n)).I) :
    (G.summandDerivedRestriction L n i).obj (G.systemObj L n) ≅ G.obj ((L.obj (op n)).obj i) :=
  Functor.piObjIso (G.summandDerivedRestriction L n) (fun i => G.obj ((L.obj (op n)).obj i)) i

/-- The transition `E_φ : Lf_φ^* E_m ⟶ E_n`: on the `i`-th summand, the isomorphism
`ρ_{a_i}` of Situation 0DC9, where `L(φ)` sends `i` to `α(i)` along `a_i`. -/
def systemMap {m n : SimplexCategory} (φ : m ⟶ n) :
    ((situation X.J (G.image L)).derivedTransitionPullback (structureSheaf X (G.image L)) φ).obj
        (G.systemObj L m) ⟶ G.systemObj L n :=
  Functor.piPreimage (G.summandDerivedRestriction L n) fun i =>
    (G.summandDerivedPullbackIso L φ i).hom.app (G.systemObj L m) ≫
      (G.restriction ((L.map φ.op).φ i)).map (G.systemObjIso L m ((L.map φ.op).f i)).hom ≫
        (G.rho ((L.map φ.op).φ i)).hom ≫ (G.systemObjIso L n i).inv

/-- The restriction of `E_φ` to the `i`-th summand. -/
theorem map_systemMap {m n : SimplexCategory} (φ : m ⟶ n) (i : (L.obj (op n)).I) :
    (G.summandDerivedRestriction L n i).map (G.systemMap L φ) =
      (G.summandDerivedPullbackIso L φ i).hom.app (G.systemObj L m) ≫
        (G.restriction ((L.map φ.op).φ i)).map (G.systemObjIso L m ((L.map φ.op).f i)).hom ≫
          (G.rho ((L.map φ.op).φ i)).hom ≫ (G.systemObjIso L n i).inv :=
  Functor.map_piPreimage _ _ i

/-- Transport of `ρ_{k_i}` composed with `systemObjIso` along an equality `k = k'`. -/
theorem restriction_map_systemObjIso_hom_rho_eqToHom {n l : SimplexCategory}
    {k k' : L.obj (op n) ⟶ L.obj (op l)} (h : k = k') (i : (L.obj (op n)).I) :
    (G.restriction (k.φ i)).map (G.systemObjIso L l (k.f i)).hom ≫ (G.rho (k.φ i)).hom =
      (eqToHom (congrArg (fun k => G.summandDerivedRestrictionAlong L k i) h)).app
          (G.systemObj L l) ≫
        (G.restriction (k'.φ i)).map (G.systemObjIso L l (k'.f i)).hom ≫ (G.rho (k'.φ i)).hom := by
  subst h
  simp

/-- The transitions `E_φ` are compatible with composition. -/
theorem systemMap_comp {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    ((situation X.J (G.image L)).derivedTransitionCompComparison (structureSheaf X (G.image L))
        ψ φ).app (G.systemObj L l) ≫ G.systemMap L (ψ ≫ φ) =
      ((situation X.J (G.image L)).derivedTransitionPullback (structureSheaf X (G.image L))
        φ).map (G.systemMap L ψ) ≫ G.systemMap L φ := by
  refine Functor.pi_hom_ext (G.summandDerivedRestriction L n) fun i => ?_
  have kc := NatTrans.congr_app (G.summandDerivedPullbackIso_comp L ψ φ i) (G.systemObj L l)
  have nτ := (G.summandDerivedPullbackIso L φ i).hom.naturality (G.systemMap L ψ)
  have mψ := G.map_systemMap L ψ ((L.map φ.op).f i)
  have coc := G.cocycle ((L.map φ.op).φ i) ((L.map ψ.op).φ ((L.map φ.op).f i))
  have nrc := (G.restrictionComp ((L.map φ.op).φ i)
    ((L.map ψ.op).φ ((L.map φ.op).f i))).inv.naturality
      (G.systemObjIso L l ((L.map ψ.op).f ((L.map φ.op).f i))).hom
  have tr := G.restriction_map_systemObjIso_hom_rho_eqToHom L (L.map_comp φ.op ψ.op) i
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Functor.comp_map] at kc nτ nrc
  rw [Functor.map_comp, Functor.map_comp, map_systemMap, map_systemMap]
  have := cocycle_chase (G.restriction ((L.map φ.op).φ i))
    (G.restriction ((L.map ψ.op).φ ((L.map φ.op).f i)))
    (G.restriction ((L.map φ.op).φ i ≫ (L.map ψ.op).φ ((L.map φ.op).f i)))
    (G.restrictionComp ((L.map φ.op).φ i) ((L.map ψ.op).φ ((L.map φ.op).f i)))
    ((G.summandDerivedRestriction L n i).map
      (((situation X.J (G.image L)).derivedTransitionCompComparison (structureSheaf X (G.image L))
        ψ φ).app (G.systemObj L l)))
    ((G.summandDerivedPullbackIso L (ψ ≫ φ) i).hom.app (G.systemObj L l))
    ((G.restriction ((L.map (ψ ≫ φ).op).φ i)).map
      (G.systemObjIso L l ((L.map (ψ ≫ φ).op).f i)).hom)
    (G.rho ((L.map (ψ ≫ φ).op).φ i)).hom (G.systemObjIso L n i).inv
    ((eqToHom (congrArg (fun k => G.summandDerivedRestrictionAlong L k i)
      (L.map_comp φ.op ψ.op))).app (G.systemObj L l))
    (G.systemObjIso L l ((L.map ψ.op).f ((L.map φ.op).f i))).hom
    (G.rho ((L.map φ.op).φ i ≫ (L.map ψ.op).φ ((L.map φ.op).f i))).hom
    ((G.summandDerivedPullbackIso L φ i).hom.app
      (((situation X.J (G.image L)).derivedTransitionPullback (structureSheaf X (G.image L))
        ψ).obj (G.systemObj L l)))
    ((G.summandDerivedPullbackIso L ψ ((L.map φ.op).f i)).hom.app (G.systemObj L l))
    ((G.summandDerivedRestriction L n i).map
      (((situation X.J (G.image L)).derivedTransitionPullback (structureSheaf X (G.image L))
        φ).map (G.systemMap L ψ)))
    ((G.summandDerivedPullbackIso L φ i).hom.app (G.systemObj L m))
    (G.systemObjIso L m ((L.map φ.op).f i)) (G.rho ((L.map φ.op).φ i)).hom
    ((G.summandDerivedRestriction L m ((L.map φ.op).f i)).map (G.systemMap L ψ))
    (G.rho ((L.map ψ.op).φ ((L.map φ.op).f i))) tr kc nτ mψ coc nrc
  convert this using 2

/-- **The simplicial system `(E_n, E_φ)` of the proof of Stacks 0DCA**, a simplicial system of
the derived category of modules on `((C/K)_total, a⁻¹O_C)` in the sense of Stacks 0D9N: `E_n`
is the formal product of the `E_{U_{n,i}}` and `E_φ` is the formal product of the
isomorphisms `ρ_a` of Situation 0DC9. -/
def localSystem : SimplicialSiteSituation.SimplicialDerivedModuleSystem (situation X.J (G.image L))
    (structureSheaf X (G.image L)) where
  obj := G.systemObj L
  map := G.systemMap L
  map_comp := G.systemMap_comp L

/-- The objects of `localSystem` are the `E_n`. -/
theorem localSystem_obj (n : SimplexCategory) : (G.localSystem L).obj n = G.systemObj L n := rfl

/-- The transitions of `localSystem` are the `E_φ`. -/
theorem localSystem_map {m n : SimplexCategory} (φ : m ⟶ n) :
    (G.localSystem L).map φ = G.systemMap L φ := rfl

/-- **The system of the locally given objects is cartesian**: its transitions are the formal
products of the isomorphisms `ρ_a`. -/
theorem localSystem_cartesian : (G.localSystem L).Cartesian := by
  intro m n φ
  rw [localSystem_map]
  have : IsIso ((Functor.pi' (G.summandDerivedRestriction L n)).map (G.systemMap L φ)) := by
    rw [isIso_pi_iff]
    intro i
    change IsIso ((G.summandDerivedRestriction L n i).map (G.systemMap L φ))
    rw [map_systemMap]
    infer_instance
  exact (Functor.FullyFaithful.ofFullyFaithful
    (Functor.pi' (G.summandDerivedRestriction L n))).isIso_of_isIso_map (G.systemMap L φ)

/-! ### Objects restricting to the locally given objects compatibly -/

/-- **An identification of the summandwise restrictions of `E` with the locally given objects,
compatible with the isomorphisms `ρ_a`.** For every summand `C/u(U_{n,i})` of every simplicial
degree, an isomorphism `σ_{n,i}` of the restriction of `E` with `E_{U_{n,i}}`, such that for
`φ : [m] ⟶ [n]`, with `L(φ)` sending `i` to `j` along `a`, the transition of `E` along `φ`,
read on the `i`-th summand, is `ρ_a` under `σ_{n,i}` and `σ_{m,j}`. This is the clause
"the restriction of `E` to `D(O_{C/u(U_{n,i})})` is `E_{U_{n,i}}` compatibly" of Stacks 0DCA. -/
structure SummandIdentification
    (E : DerivedCategory ((situation X.J (G.image L)).totalRingedTopos
      (structureSheaf X (G.image L))).Modules) where
  /-- The identification of the `i`-th summand of the degree-`n` restriction with
  `E_{U_{n,i}}`. -/
  iso : ∀ (n : SimplexCategory) (i : (L.obj (op n)).I),
    (G.summandDerivedRestriction L n i).obj
        (((situation X.J (G.image L)).derivedModuleSystem (structureSheaf X (G.image L)) E).obj n) ≅
      G.obj ((L.obj (op n)).obj i)
  /-- The transitions of `E` are the isomorphisms `ρ_a` of Situation 0DC9. -/
  comm : ∀ {m n : SimplexCategory} (φ : m ⟶ n) (i : (L.obj (op n)).I),
    (G.summandDerivedRestriction L n i).map
        (((situation X.J (G.image L)).derivedModuleSystem (structureSheaf X (G.image L)) E).map φ) ≫
      (iso n i).hom =
      (G.summandDerivedPullbackIso L φ i).hom.app
          (((situation X.J (G.image L)).derivedModuleSystem (structureSheaf X (G.image L))
            E).obj m) ≫
        (G.restriction ((L.map φ.op).φ i)).map (iso m ((L.map φ.op).f i)).hom ≫
          (G.rho ((L.map φ.op).φ i)).hom

variable {G L} in
/-- An identification of the simplicial system of `E` with the system of the locally given
objects gives an identification of the summandwise restrictions of `E`. -/
def SummandIdentification.ofSystemIso
    {E : DerivedCategory ((situation X.J (G.image L)).totalRingedTopos
      (structureSheaf X (G.image L))).Modules}
    (e : (situation X.J (G.image L)).derivedModuleSystem (structureSheaf X (G.image L)) E ≅
      G.localSystem L) : G.SummandIdentification L E where
  iso n i := (G.summandDerivedRestriction L n i).mapIso
      ((SimplicialSiteSituation.SimplicialDerivedModuleSystem.evaluation n).mapIso e) ≪≫
    G.systemObjIso L n i
  comm {m n} φ i :=
    summand_chase ((situation X.J (G.image L)).derivedTransitionPullback
        (structureSheaf X (G.image L)) φ) (G.summandDerivedRestriction L n i)
      (G.summandDerivedRestriction L m ((L.map φ.op).f i)) (G.restriction ((L.map φ.op).φ i))
      (G.summandDerivedPullbackIso L φ i).hom
      (((situation X.J (G.image L)).derivedModuleSystem (structureSheaf X (G.image L)) E).map φ)
      (G.systemMap L φ)
      ((SimplicialSiteSituation.SimplicialDerivedModuleSystem.evaluation m).mapIso e)
      ((SimplicialSiteSituation.SimplicialDerivedModuleSystem.evaluation n).mapIso e)
      (e.hom.naturality φ) (G.systemObjIso L m ((L.map φ.op).f i)) (G.systemObjIso L n i)
      (G.rho ((L.map φ.op).φ i)).hom (G.map_systemMap L φ i)

variable {G L} in
/-- A summandwise identification of `E` with the locally given objects identifies the
simplicial system of `E` with the system of the locally given objects. -/
def SummandIdentification.systemIso
    {E : DerivedCategory ((situation X.J (G.image L)).totalRingedTopos
      (structureSheaf X (G.image L))).Modules} (σ : G.SummandIdentification L E) :
    (situation X.J (G.image L)).derivedModuleSystem (structureSheaf X (G.image L)) E ≅
      G.localSystem L :=
  SimplicialSiteSituation.SimplicialDerivedModuleSystem.isoMk _ _
    (fun n => (Functor.FullyFaithful.ofFullyFaithful
      (Functor.pi' (G.summandDerivedRestriction L n))).preimageIso
        (Pi.isoMk fun i => σ.iso n i ≪≫ (G.systemObjIso L n i).symm))
    fun {m n} φ => Functor.pi_hom_ext (G.summandDerivedRestriction L n) fun i => by
      rw [Functor.map_comp, Functor.map_comp]
      exact system_chase ((situation X.J (G.image L)).derivedTransitionPullback
          (structureSheaf X (G.image L)) φ) (G.summandDerivedRestriction L n i)
        (G.summandDerivedRestriction L m ((L.map φ.op).f i)) (G.restriction ((L.map φ.op).φ i))
        (G.summandDerivedPullbackIso L φ i).hom
        (((situation X.J (G.image L)).derivedModuleSystem (structureSheaf X (G.image L)) E).map φ)
        (G.systemMap L φ) (G.systemObjIso L m ((L.map φ.op).f i)) (G.systemObjIso L n i)
        (G.rho ((L.map φ.op).φ i)).hom (σ.iso m ((L.map φ.op).f i)) (σ.iso n i) _ _
        (congrFun ((Functor.pi' (G.summandDerivedRestriction L m)).map_preimage _)
          ((L.map φ.op).f i))
        (congrFun ((Functor.pi' (G.summandDerivedRestriction L n)).map_preimage _) i)
        (G.map_systemMap L φ i) (σ.comm φ i)

variable {G L} in
/-- The restriction of `systemIso` to the `i`-th summand of degree `n`. -/
theorem SummandIdentification.map_systemIso_hom_app
    {E : DerivedCategory ((situation X.J (G.image L)).totalRingedTopos
      (structureSheaf X (G.image L))).Modules} (σ : G.SummandIdentification L E)
    (n : SimplexCategory) (i : (L.obj (op n)).I) :
    (G.summandDerivedRestriction L n i).map (σ.systemIso.hom.app n) =
      (σ.iso n i).hom ≫ (G.systemObjIso L n i).inv :=
  congrFun ((Functor.pi' (G.summandDerivedRestriction L n)).map_preimage _) i

end Derived

end AlgebraicGeometry.RingedSite.LocallyGiven

end
