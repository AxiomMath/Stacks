module

public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.SheafHom
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.FirstCohomology
public import StacksFrontier.CategoryTheory.Sites.Modules.InvertibleRankOne
public import StacksFrontier.CategoryTheory.Sites.Modules.UnitsSheaf
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Torsors under the units of a ringed site and invertible modules

Let `(C, O)` be a locally ringed site. The sections of an invertible `O`-module `L` by which
multiplication is bijective — its *local generators* — form a sheaf of sets `L^*` on which the
sheaf of units `O^*` acts simply transitively, and which is locally nonempty because an
invertible module on a locally ringed site is locally free of rank one (Stacks 0B8Q). So `L^*`
is an `O^*`-torsor. Conversely, from an `O^*`-torsor `F` one builds an `O`-module whose sections
over an object `U` are the `O^*`-equivariant maps from the sections of `F` over the slice over
`U` to the sections of `O`; that module is invertible, and its torsor of local generators is
isomorphic to `F`.

This file constructs both directions and the compatibility of the construction with isomorphisms
of modules. The resulting isomorphism between the Picard group and first cohomology of `O^*`
is assembled in
`StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.PicardGroupOfARingedSite`.

## Main definitions

* `Stacks.Cohomology.Torsors.Generators.unitsAddSheaf`: the sheaf of units of the structure
  sheaf, written additively so that it is a coefficient sheaf for cohomology.
* `Stacks.Cohomology.Torsors.Generators.GeneratorSections`: the local generators of a sheaf of
  modules over an object.
* `Stacks.Cohomology.Torsors.Generators.generatorSectionsSheaf`: the sheaf of local generators.
* `Stacks.Cohomology.Torsors.Generators.GeneratorTorsor`: a torsor under the units together with
  the identification of its sections with the local generators of a module.
* `Stacks.Cohomology.Torsors.Generators.generatorTorsor`: the generator torsor of an invertible
  module on a locally ringed site.
* `Stacks.Cohomology.Torsors.Generators.coefficientSheaf`: the invertible module attached to a
  torsor under the units.

## Main results

* `Stacks.Cohomology.Torsors.Generators.exists_cover_generatorSections`: an invertible module on
  a locally ringed site has local generators over a covering of every object.
* `Stacks.Cohomology.Torsors.Generators.generatorSectionTrivialization`: a local generator
  trivializes the module on the slice site.
* `Stacks.Cohomology.Torsors.Generators.coefficientSheaf_isInvertible`: the module attached to a
  torsor is invertible.
* `Stacks.Cohomology.Torsors.Generators.coefficientGeneratorTorsor_isIsomorphic`: its generator
  torsor is the torsor one started from, so the construction is essentially surjective.
* `Stacks.Cohomology.Torsors.Generators.generatorTorsor_isIsomorphic_of_iso`: isomorphic modules
  have isomorphic generator torsors.

## Implementation notes

The sheaf of units is `AlgebraicGeometry.RingedSite.unitsSheaf` of Tag 0409, valued in
`CommGrpCat`; cohomology takes coefficients in `AddCommGrpCat`, so it is transported along the
standard equivalence of the two categories of commutative groups. Torsors are the ones of Tag
03AH, and `Stacks.Cohomology.Torsors.AbelianTorsor` is a torsor under the multiplicatively
written group sheaf of an abelian sheaf; a section of the units therefore appears as
`Multiplicative.ofAdd (Additive.ofMul a)`.

A local generator over `U` is asked to generate over *every* arrow into `U`, not only over `U`
itself. That is what makes the generators a subsheaf of the module — the condition is stable
under restriction by construction — and it is also what a trivialization of the module on the
slice site over `U` provides. The sheaf condition for the subfunctor of generators is the
statement that a section generating locally generates, which is proved by transporting the
multiplication map to the slice site, where generation over every object is bijectivity of a
morphism of sheaves.

`GeneratorTorsor` is a structure rather than a bare torsor so that the identification of its
sections with the generators, its compatibility with restriction, and the fact that the action
of a unit is multiplication are all available; the construction from an invertible module
produces the identity identification, but the three properties are what every later argument
uses, and stating them keeps those arguments independent of the construction.

The module attached to a torsor is built as a presheaf of modules whose sections over `U` are
the families assigning to every section of the torsor over an object of the slice over `U` a
section of `O`, compatibly with restriction and with the unit action twisted by inversion. The
sheaf condition is obtained by identifying that presheaf with a subfunctor of the internal hom
presheaf `presheafHom`, which is a sheaf by `CategoryTheory.Presheaf.IsSheaf.hom`.

## References

* [Stacks Project, Tag 040E](https://stacks.math.columbia.edu/tag/040E)
* [Stacks Project, Tag 03AH](https://stacks.math.columbia.edu/tag/03AH)
* [Stacks Project, Tag 03AI](https://stacks.math.columbia.edu/tag/03AI)
* [Stacks Project, Tag 0409](https://stacks.math.columbia.edu/tag/0409)
* [Stacks Project, Tag 0B8Q](https://stacks.math.columbia.edu/tag/0B8Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u v w

namespace Stacks.Cohomology.Torsors.Generators

/-! ### The sheaf of units as a coefficient sheaf -/

/-- The sheaf of units `O^*` of a ringed site, written additively so that it can be used as a
coefficient sheaf for cohomology. -/
def unitsAddSheaf (X : RingedSite.{u, v, w}) : Sheaf X.J AddCommGrpCat.{w} := by
  letI : Limits.PreservesLimitsOfSize.{max u v, max u v} CommGrpCat.toAddCommGrp.{w} :=
    commGroupAddCommGroupEquivalence.symm.toAdjunction.rightAdjoint_preservesLimits
  exact (sheafCompose X.J CommGrpCat.toAddCommGrp).obj
    (AlgebraicGeometry.RingedSite.unitsSheaf X)

/-! ### Local generators of a sheaf of modules -/

/-- The *local generators* of a sheaf of modules over an object `U` of a ringed site: the
sections over `U` by which multiplication is bijective over every arrow into `U`. -/
abbrev GeneratorSections (X : RingedSite.{u, u, u})
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (U : X.C) :=
  {s : L.val.obj (op U) //
    ∀ (V : X.C) (f : V ⟶ U),
      Function.Bijective (fun r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V) =>
        r • L.val.restrictₛₗ f.op s)}

/-- Two local generators over the same object differ by a unique unit. -/
theorem existsUnique_unit_smul_generatorSections
    (X : RingedSite.{u, u, u}) (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (U : X.C) (s t : GeneratorSections X L U) :
    ∃! a : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U) : Type u)ˣ,
      a.val • s.val = t.val := by
  let R := ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U) : Type u)
  let : CommRing R := inferInstanceAs (CommRing (X.O.obj.obj (op U)))
  have hs : Function.Bijective (fun r : R => r • s.val) := by
    simpa using s.property U (𝟙 U)
  have ht : Function.Bijective (fun r : R => r • t.val) := by
    simpa using t.property U (𝟙 U)
  obtain ⟨r, hr⟩ := hs.2 t.val
  obtain ⟨q, hq⟩ := ht.2 s.val
  change r • s.val = t.val at hr
  change q • t.val = s.val at hq
  have hqr : q * r = 1 := by
    apply hs.1
    calc
      (q * r) • s.val = q • (r • s.val) := by rw [mul_smul]
      _ = q • t.val := by rw [hr]
      _ = s.val := hq
      _ = 1 • s.val := (one_smul R s.val).symm
  refine ⟨⟨r, q, (mul_comm r q).trans hqr, hqr⟩, hr, fun b hb => Units.ext (hs.1 ?_)⟩
  exact hb.trans hr.symm

/-! ### Two generalities on colimits and on sheaves -/

/-- A one-element cofan which is a colimit has an invertible leg. -/
theorem cofanFinOne_inj_isIso {D : Type u} [Category.{v} D]
    {A B : D} (f : Fin 1 → (A ⟶ B))
    (hf : IsColimit (Cofan.mk B f)) (i : Fin 1) : IsIso (f i) := by
  let c₀ : Cofan (fun _ : Fin 1 => A) := Cofan.mk A (fun _ => 𝟙 A)
  have hc₀ : IsColimit c₀ := by
    refine ⟨(fun t => t.ι.app (Discrete.mk (0 : Fin 1))), ?_, ?_⟩
    · intro t j
      have hj : j = ⟨(0 : Fin 1)⟩ := Subsingleton.elim _ _
      subst j
      simp [c₀]
    · intro t m hm
      simpa [c₀] using hm (Discrete.mk (0 : Fin 1))
  let e := IsColimit.coconePointUniqueUpToIso hf hc₀
  have h0 : f 0 ≫ e.hom = 𝟙 A := by
    simpa [e, c₀] using IsColimit.comp_coconePointUniqueUpToIso_hom hf hc₀ ⟨(0 : Fin 1)⟩
  obtain rfl : i = 0 := Subsingleton.elim _ _
  rw [(cancel_mono e.hom).1 (h0.trans e.inv_hom_id.symm)]
  infer_instance

/-- An isomorphism exhibits its target as a one-element coproduct of its source. -/
def cofanFinOneIsColimitOfIso {D : Type u} [Category.{v} D]
    {A B : D} (e : A ≅ B) : IsColimit (Cofan.mk B (fun _ : Fin 1 => e.hom)) where
  desc t := e.inv ≫ t.ι.app ⟨0⟩
  fac t j := by
    have hj : j = ⟨(0 : Fin 1)⟩ := Subsingleton.elim _ _
    subst j
    simp
  uniq t m hm := by
    apply (cancel_epi e.hom).1
    simpa using hm ⟨(0 : Fin 1)⟩

/-- A morphism of sheaves of sets which is bijective on the members of a covering of `U` is
bijective over `U`. -/
theorem bijective_of_bijective_on_cover
    {D : Type u} [Category.{v} D] (J : GrothendieckTopology D)
    {F G : Dᵒᵖ ⥤ Type w} (hF : Presheaf.IsSheaf J F)
    (hG : Presheaf.IsSheaf J G) {U : D} (S : Sieve U) (hS : S ∈ J U)
    (φ : F ⟶ G)
    (hφ : ∀ ⦃V : D⦄ (f : V ⟶ U), S f → Function.Bijective (φ.app (op V))) :
    Function.Bijective (φ.app (op U)) := by
  have hFS := hF.isSheafFor S hS
  have hGS := hG.isSheafFor S hS
  constructor
  · intro x y hxy
    apply hFS.isSeparatedFor.ext
    intro V f hf
    apply (hφ f hf).1
    calc
      φ.app (op V) (F.map f.op x) = G.map f.op (φ.app (op U) x) :=
            NatTrans.naturality_apply φ f.op x
      _ = G.map f.op (φ.app (op U) y) := by rw [hxy]
      _ = φ.app (op V) (F.map f.op y) := (NatTrans.naturality_apply φ f.op y).symm
  · intro y
    let xloc : Presieve.FamilyOfElements F S.arrows := fun V f hf =>
      Classical.choose ((hφ f hf).2 (G.map f.op y))
    have hxloc (V : D) (f : V ⟶ U) (hf : S f) :
        φ.app (op V) (xloc f hf) = G.map f.op y :=
      Classical.choose_spec ((hφ f hf).2 (G.map f.op y))
    have hcompat : xloc.Compatible := by
      intro V₁ V₂ W g₁ g₂ f₁ f₂ h₁ h₂ hcomp
      have hh₁ : S (g₁ ≫ f₁) := S.downward_closed h₁ g₁
      apply (hφ (g₁ ≫ f₁) hh₁).1
      calc
        φ.app (op W) (F.map (g₁.op) (xloc f₁ h₁)) =
            G.map (g₁.op) (φ.app (op V₁) (xloc f₁ h₁)) :=
              NatTrans.naturality_apply φ g₁.op (xloc f₁ h₁)
        _ = G.map (g₁.op) (G.map f₁.op y) := by rw [hxloc V₁ f₁ h₁]
        _ = G.map (g₂.op) (G.map f₂.op y) := by
              have hOpp : f₁.op ≫ g₁.op = f₂.op ≫ g₂.op := by
                simpa only [← op_comp] using congrArg Quiver.Hom.op hcomp
              change ((G.map f₁.op) ≫ (G.map g₁.op)) y =
                ((G.map f₂.op) ≫ (G.map g₂.op)) y
              rw [← Functor.map_comp, ← Functor.map_comp, hOpp]
        _ = G.map (g₂.op) (φ.app (op V₂) (xloc f₂ h₂)) := by
              rw [hxloc V₂ f₂ h₂]
        _ = φ.app (op W) (F.map (g₂.op) (xloc f₂ h₂)) :=
              (NatTrans.naturality_apply φ g₂.op (xloc f₂ h₂)).symm
    let x := hFS.amalgamate xloc hcompat
    refine ⟨x, ?_⟩
    apply hGS.isSeparatedFor.ext
    intro V f hf
    calc
      G.map f.op (φ.app (op U) x) = φ.app (op V) (F.map f.op x) :=
            (NatTrans.naturality_apply φ f.op x).symm
      _ = φ.app (op V) (xloc f hf) := by
            rw [hFS.valid_glue (x := xloc) (hx := hcompat) f hf]
      _ = G.map f.op y := hxloc V f hf

/-! ### Generators from a trivialization, and local existence -/

/-- The image of `1` under a trivialization of a module on the slice site over `U` is a local
generator over `U`. -/
def generatorSections_of_isIso_unitHom
    (X : RingedSite.{u, u, u}) (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (U : X.C)
    (f : SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) ⟶ L.over U)
    (hf : IsIso f) : GeneratorSections X L U := by
  let s := (L.over U).unitHomEquiv f
  let sU := s.val (op (Over.mk (𝟙 U)))
  have hfEq : (L.over U).unitHomEquiv.symm s = f :=
    (L.over U).unitHomEquiv.symm_apply_apply f
  refine ⟨sU, ?_⟩
  intro V g
  let : CommRing ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V) : Type u) :=
    inferInstanceAs (CommRing (X.O.obj.obj (op V)))
  have hbij : Function.Bijective
      (fun r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V) =>
        r • L.val.restrictₛₗ g.op sU) := by
    have hcomp : IsIso (f.val.app (op (Over.mk g))) :=
      Functor.map_isIso
        (PresheafOfModules.evaluation ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U).obj
          (op (Over.mk g)))
          ((SheafOfModules.forget ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)).map f)
    have hfun : (fun r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V) =>
        r • L.val.restrictₛₗ g.op sU) =
        ⇑(f.val.app (op (Over.mk g))).hom := by
      have hval : ((SheafOfModules.forget ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)).map
          ((L.over U).unitHomEquiv.symm s)) = (L.over U).val.unitHomEquiv.symm s := by
        simp only [SheafOfModules.unitHomEquiv]
        rfl
      have hsval : s.val (op (Over.mk g)) = (L.val.map g.op).hom sU :=
        (s.property (Over.homMk g (by simp) : Over.mk g ⟶ Over.mk (𝟙 U)).op).symm
      funext r
      rw [← hfEq]
      change r • (L.val.map g.op).hom sU =
        (((SheafOfModules.forget ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)).map
          ((L.over U).unitHomEquiv.symm s)).app (op (Over.mk g))).hom r
      rw [hval, ← hsval]
      simp only [PresheafOfModules.unitHomEquiv, Equiv.coe_fn_symm_mk]
      rfl
    rw [hfun]
    exact (ConcreteCategory.isIso_iff_bijective _).1 hcomp
  exact hbij

/-- **Local existence of generators.** On a locally ringed site an invertible module has a local
generator over each member of a covering of every object; this is Stacks 0B8Q. -/
theorem exists_cover_generatorSections
    (X : RingedSite.{u, u, u})
    (hX : AlgebraicGeometry.RingedSite.IsLocallyRinged X)
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hL : Stacks.SheafOfModules.IsInvertible X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L)
    (U : X.C) :
    ∃ (I : Type u) (V : I → X.C) (f : ∀ i, V i ⟶ U),
      Sieve.ofArrows V f ∈ X.J U ∧ ∀ i, Nonempty (GeneratorSections X L (V i)) := by
  have hfree :=
    (AlgebraicGeometry.RingedSite.isInvertible_iff_isFiniteLocallyFreeOfRank_one X L hX).1 hL
  obtain ⟨I, V, f, hcover, hlocal⟩ := hfree U
  refine ⟨I, V, f, hcover, ?_⟩
  intro i
  obtain ⟨ι, ⟨hcol⟩⟩ := hlocal i
  let : IsColimit (Cofan.mk (L.over (V i)) ι) := hcol
  let : IsIso (ι 0) := cofanFinOne_inj_isIso ι hcol 0
  exact ⟨generatorSections_of_isIso_unitHom X L (V i) (ι 0) (by infer_instance)⟩

/-- Restricting a local generator gives a local generator. -/
def generatorSections_restrict
    (X : RingedSite.{u, u, u}) (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    {U V : X.C} (f : V ⟶ U) (s : GeneratorSections X L U) :
    GeneratorSections X L V := by
  refine ⟨L.val.restrictₛₗ f.op s.val, ?_⟩
  intro W g
  have h := s.property W (g ≫ f)
  have heq :
      (fun r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W) =>
        r • L.val.restrictₛₗ g.op (L.val.restrictₛₗ f.op s.val)) =
      (fun r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W) =>
        r • L.val.restrictₛₗ (g ≫ f).op s.val) := by
    funext r
    simp only [PresheafOfModules.restrictₛₗ_apply, op_comp]
    exact congrArg (fun t => r • t) (L.val.map_comp_apply f.op g.op s.val).symm
  rw [heq]
  exact h

/-- The restrictions of a module section to all objects of the slice form a section of the
relocalized module. -/
def generatorSections_overSections
    (X : RingedSite.{u, u, u}) (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (U : X.C) (s : L.val.obj (op U)) : (L.over U).val.sections := by
  refine PresheafOfModules.sectionsMk (fun Y => L.val.restrictₛₗ Y.unop.hom.op s) ?_
  intro Y Z f
  change L.val.map f.unop.left.op (L.val.map Y.unop.hom.op s) = L.val.map Z.unop.hom.op s
  rw [← L.val.map_comp_apply, ← op_comp, Over.w f.unop]

/-- The morphism out of the unit module attached to a section is multiplication by that
section. -/
theorem unitHom_symm_app_smul
    {D : Type u} [Category.{v} D] (J : GrothendieckTopology D)
    {R : Sheaf J RingCat.{u}} (M : SheafOfModules R)
    (s : M.sections) (V : Dᵒᵖ) (a : (R.obj.obj V : Type u)) :
    (ConcreteCategory.hom ((M.unitHomEquiv.symm s).val.app V)) a =
      ((LinearMap.ringLmapEquivSelf (R.obj.obj V) ℤ (M.val.obj V)).symm (s.eval V)) a := by
  simp only [SheafOfModules.unitHomEquiv, PresheafOfModules.unitHomEquiv]
  rfl

/-- **A section which generates locally generates.** If a section over `U` generates after
restriction along the members of a covering of `U`, it is a local generator over `U`. -/
def generatorSections_of_locally_generator
    (X : RingedSite.{u, u, u}) (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (U : X.C) (s : L.val.obj (op U))
    (S : Sieve U) (hS : S ∈ X.J U)
    (hlocal : ∀ ⦃V : X.C⦄ (f : V ⟶ U), S f →
      ∀ (W : X.C) (g : W ⟶ V), Function.Bijective
        (fun r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W) =>
          r • L.val.restrictₛₗ (g ≫ f).op s)) :
    GeneratorSections X L U := by
  let U₀ : Over U := Over.mk (𝟙 U)
  let S' : Sieve U₀ := (Sieve.overEquiv U₀).symm S
  have hS' : S' ∈ (X.J.over U) U₀ := X.J.overEquiv_symm_mem_over U₀ S hS
  let M := L.over U
  let R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U
  let N := SheafOfModules.unit R
  let sec := generatorSections_overSections X L U s
  let f : N ⟶ M := M.unitHomEquiv.symm sec
  let F := (SheafOfModules.toSheaf R).obj N
  let G := (SheafOfModules.toSheaf R).obj M
  have hF : Presheaf.IsSheaf (X.J.over U) (F.obj ⋙ forget AddCommGrpCat) :=
    Presheaf.isSheaf_comp_of_isSheaf _ _ (forget AddCommGrpCat) F.property
  have hG : Presheaf.IsSheaf (X.J.over U) (G.obj ⋙ forget AddCommGrpCat) :=
    Presheaf.isSheaf_comp_of_isSheaf _ _ (forget AddCommGrpCat) G.property
  let φ : (F.obj ⋙ forget AddCommGrpCat) ⟶ (G.obj ⋙ forget AddCommGrpCat) :=
    Functor.whiskerRight ((SheafOfModules.toSheaf R).map f).hom (forget AddCommGrpCat)
  have hform (V : Over U) (r : (R.obj.obj (op V) : Type u)) :
      φ.app (op V) r = r • sec.eval (op V) := by
    change (ConcreteCategory.hom (f.val.app (op V))) r = r • sec.eval (op V)
    rw [unitHom_symm_app_smul (X.J.over U) M sec (op V) r]
    simp [LinearMap.ringLmapEquivSelf]
  have hφ : ∀ ⦃V : Over U⦄ (g : V ⟶ U₀), S' g →
      Function.Bijective (φ.app (op V)) := by
    intro V g hg
    have hbase : S g.left := (Sieve.overEquiv_symm_iff S g).mp hg
    have hV : V.hom = g.left := by simpa [U₀] using (Over.w g).symm
    let t : GeneratorSections X L V.left := by
      refine ⟨L.val.restrictₛₗ g.left.op s, ?_⟩
      intro W k
      have heq :
          (fun r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W) =>
            r • L.val.restrictₛₗ k.op (L.val.restrictₛₗ g.left.op s)) =
          (fun r => r • L.val.restrictₛₗ (k ≫ g.left).op s) := by
        funext r
        simp only [PresheafOfModules.restrictₛₗ_apply, op_comp]
        exact congrArg (fun z => r • z) (L.val.map_comp_apply g.left.op k.op s).symm
      rw [heq]
      exact hlocal g.left hbase W k
    have hgen : Function.Bijective
        (fun r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V.left) =>
          r • t.val) := by
      simpa using t.property V.left (𝟙 V.left)
    have htval : t.val = sec.eval (op V) := by
      change L.val.map g.left.op s = L.val.map V.hom.op s
      rw [hV]
    let : Module (R.obj.obj (op V) : Type u) (M.val.obj (op V) : Type u) :=
      (L.val.obj (op V.left)).isModule
    have hgenSec : Function.Bijective
        (fun r : (R.obj.obj (op V) : Type u) => r • sec.eval (op V)) := by
      convert hgen using 1
      · rfl
      · rfl
      · rw [htval]
        exact HEq.rfl
    have hfun : ⇑(φ.app (op V)) =
        (fun r : (R.obj.obj (op V) : Type u) => r • sec.eval (op V)) := by
      funext r
      exact hform V r
    rw [hfun]
    exact hgenSec
  have hbij : ∀ (T : Over U), Function.Bijective (φ.app (op T)) := by
    intro T
    let p : T ⟶ U₀ := Over.homMk T.hom (by simp [U₀])
    let Rcover : Sieve T := S'.pullback p
    have hRcover : Rcover ∈ (X.J.over U) T := (X.J.over U).pullback_stable _ hS'
    exact bijective_of_bijective_on_cover (X.J.over U) hF hG
      Rcover hRcover φ (fun V g hg => hφ (g ≫ p) hg)
  refine ⟨s, ?_⟩
  intro V g
  let qV : Over U := Over.mk g
  have hqV : Function.Bijective (φ.app (op qV)) := hbij qV
  let : Module (R.obj.obj (op qV) : Type u) ((L.over U).val.obj (op qV) : Type u) :=
    ((L.over U).val.obj (op qV)).isModule
  let : Module ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V) : Type u)
      (L.val.obj (op V) : Type u) :=
    (L.val.obj (op V)).isModule
  let : Module (R.obj.obj (op qV) : Type u) (L.val.obj (op V) : Type u) :=
    (L.val.obj (op V)).isModule
  change Function.Bijective
    (fun r : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V) : Type u) =>
      r • (L.val.restrictₛₗ g.op s : L.val.obj (op V)))
  have hfun : ⇑(ConcreteCategory.hom (φ.app (op qV))) =
      (fun r : (R.obj.obj (op qV) : Type u) => r • sec.eval (op qV)) := by
    funext r
    exact hform qV r
  have hsec : sec.eval (op qV) = L.val.restrictₛₗ g.op s := by
    change L.val.map g.op s = L.val.map g.op s
    rfl
  have hgenSlice : Function.Bijective
      (fun r : (R.obj.obj (op qV) : Type u) => r • sec.eval (op qV)) := by
    change Function.Bijective (⇑(ConcreteCategory.hom (φ.app (op qV))))
    rw [hfun]
    exact hqV
  convert hgenSlice using 1
  · rfl
  · rfl
  · rw [← hsec]
    exact HEq.rfl

/-! ### The sheaf of local generators -/

/-- The local generators as a subfunctor of the underlying presheaf of sets of a module. -/
def generatorSectionsSubfunctor
    (X : RingedSite.{u, u, u})
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    Subfunctor (L.val.presheaf ⋙ forget AddCommGrpCat) where
  obj U := {s | ∀ (V : X.C) (f : V ⟶ U.unop), Function.Bijective
    (fun r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V) =>
      r • L.val.restrictₛₗ f.op s)}
  map := by
    intro U V f s hs
    change ∀ (W : X.C) (g : W ⟶ V.unop), Function.Bijective
      (fun r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W) =>
        r • L.val.restrictₛₗ g.op (L.val.map f s))
    intro W g
    have heq :
        (fun r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W) =>
          r • L.val.restrictₛₗ g.op (L.val.map f s)) =
        (fun r => r • L.val.restrictₛₗ (g ≫ f.unop).op s) := by
      funext r
      simp only [op_comp]
      exact congrArg (fun z => r • z) (L.val.map_comp_apply f g.op s).symm
    rw [heq]
    exact hs W (g ≫ f.unop)

/-- The sheaf of local generators of a sheaf of modules. Its sheaf condition is exactly the
statement that a section which generates locally generates. -/
def generatorSectionsSheaf
    (X : RingedSite.{u, u, u})
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    Sheaf X.J (Type u) := by
  let G := generatorSectionsSubfunctor X L
  have hbase : Presieve.IsSheaf X.J (L.val.presheaf ⋙ forget AddCommGrpCat) :=
    (isSheaf_iff_isSheaf_of_type X.J _).1
      (Presheaf.isSheaf_comp_of_isSheaf X.J L.val.presheaf (forget AddCommGrpCat) L.isSheaf)
  have hG : Presieve.IsSheaf X.J G.toFunctor := by
    rw [Subfunctor.isSheaf_iff (G := G) hbase]
    intro U s hs
    change ∀ (V : X.C) (f : V ⟶ U.unop), Function.Bijective
      (fun r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V) =>
        r • L.val.restrictₛₗ f.op s)
    simpa only [generatorSections_of_locally_generator] using
      (generatorSections_of_locally_generator X L U.unop s (G.sieveOfSection s) hs (by
        intro V f hf W g
        have hmem : L.val.presheaf.map f.op s ∈ G.obj (op V) := hf
        have hbij := hmem W g
        have hmap : (ConcreteCategory.hom (L.val.presheaf.map f.op)) s =
            L.val.restrictₛₗ f.op s := rfl
        rw [hmap] at hbij
        have heq :
            (fun r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W) =>
              r • L.val.restrictₛₗ g.op (L.val.restrictₛₗ f.op s)) =
            (fun r => r • L.val.restrictₛₗ (g ≫ f).op s) := by
          funext r
          simp only [PresheafOfModules.restrictₛₗ_apply, op_comp]
          exact congrArg (fun z => r • z) (L.val.map_comp_apply f.op g.op s).symm
        simpa only [← heq] using hbij)).property
  exact ⟨G.toFunctor, (isSheaf_iff_isSheaf_of_type X.J _).2 hG⟩

/-- A unit multiple of a local generator is a local generator. -/
def generatorSections_smul_unit
    (X : RingedSite.{u, u, u}) (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (U : X.C) (a : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U) : Type u)ˣ)
    (s : GeneratorSections X L U) : GeneratorSections X L U := by
  letI : CommRing ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U) : Type u) :=
    inferInstanceAs (CommRing (X.O.obj.obj (op U)))
  refine ⟨@SMul.smul _ _ _ a.val s.val, ?_⟩
  intro V g
  let : CommRing ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V) : Type u) :=
    inferInstanceAs (CommRing (X.O.obj.obj (op V)))
  let aV : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V) : Type u)ˣ :=
    Units.map ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map g.op).hom.toMonoidHom a
  let sV := L.val.restrictₛₗ g.op s.val
  have ha : L.val.restrictₛₗ g.op (@SMul.smul _ _ _ a.val s.val) =
      @SMul.smul _ _ _ aV.val sV := by
    change L.val.restrictₛₗ g.op (a.val • s.val) =
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map g.op).hom a.val •
        L.val.restrictₛₗ g.op s.val
    exact (L.val.restrictₛₗ g.op).map_smulₛₗ a.val s.val
  have hs := s.property V g
  constructor
  · intro x y hxy
    have hxy0 : x • L.val.restrictₛₗ g.op (a.val • s.val) =
        y • L.val.restrictₛₗ g.op (a.val • s.val) := hxy
    have hxy' : (x * aV.val) • sV = (y * aV.val) • sV := calc
      (x * aV.val) • sV = x • (aV.val • sV) := by rw [mul_smul]
      _ = x • L.val.restrictₛₗ g.op (a.val • s.val) := congrArg (fun q => x • q) ha.symm
      _ = y • L.val.restrictₛₗ g.op (a.val • s.val) := hxy0
      _ = y • (aV.val • sV) := congrArg (fun q => y • q) ha
      _ = (y * aV.val) • sV := by rw [mul_smul]
    exact (Units.mul_left_inj aV).1 (hs.1 hxy')
  · intro t
    obtain ⟨z, hz⟩ := hs.2 t
    refine ⟨z * aV⁻¹, ?_⟩
    change (z * aV⁻¹) • L.val.restrictₛₗ g.op (@SMul.smul _ _ _ a.val s.val) = t
    rw [ha]
    calc
      (z * aV⁻¹) • (aV.val • sV) = ((z * aV⁻¹) * aV.val) • sV := by rw [← mul_smul]
      _ = z • sV := by simp [mul_assoc]
      _ = t := hz

/-! ### The torsor of local generators -/

/-- A torsor under the units together with the identification of its sections with the local
generators of a module, the compatibility of that identification with restriction, and the
statement that a unit acts by multiplication. -/
structure GeneratorTorsor (X : RingedSite.{u, u, u})
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) where
  /-- The torsor under the additive notation for the units sheaf. -/
  torsor : Stacks.Cohomology.Torsors.AbelianTorsor (unitsAddSheaf X)
  /-- Sections are precisely local generators. -/
  sectionsEquiv (U : X.Cᵒᵖ) : torsor.1.presheaf.obj U ≃ GeneratorSections X L U.unop
  /-- Restriction of torsor sections agrees with restriction of module sections. -/
  sectionsEquiv_restrict {U V : X.Cᵒᵖ} (f : U ⟶ V) (s : torsor.1.presheaf.obj U) :
    (sectionsEquiv V (torsor.1.presheaf.map f s)).val =
      L.val.restrictₛₗ f (sectionsEquiv U s).val
  /-- The action of a unit is multiplication on the corresponding generator. -/
  sectionsEquiv_smul (U : X.Cᵒᵖ) (a : (X.O.obj.obj U)ˣ) (s : torsor.1.presheaf.obj U) :
    (sectionsEquiv U (torsor.1.act U (Multiplicative.ofAdd (Additive.ofMul a)) s)).val =
      @SMul.smul ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U) (L.val.obj U) _ a.val
        (sectionsEquiv U s).val

/-- **The generator torsor of an invertible module.** On a locally ringed site the local
generators of an invertible module form a torsor under the sheaf of units. -/
@[ega "IV 21.13.13" "partial"]
def generatorTorsor (X : RingedSite.{u, u, u})
    (hX : AlgebraicGeometry.RingedSite.IsLocallyRinged X)
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hL : Stacks.SheafOfModules.IsInvertible X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L) :
    GeneratorTorsor X L := by
  let H := unitsAddSheaf X
  let G := Stacks.Cohomology.Torsors.abelianSheafAsGroupSheaf H
  let F : PseudoTorsor G := {
    presheaf := (generatorSectionsSheaf X L).obj
    isSheaf := (generatorSectionsSheaf X L).property
    act := by
      intro U a s
      change GeneratorSections X L U.unop at s
      letI : Module ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U : Type u)
          (L.val.obj U : Type u) :=
        (L.val.obj U).isModule
      exact generatorSections_smul_unit X L U.unop
        (Additive.toMul (Multiplicative.toAdd a)) s
    one_act := by
      intro U s
      change GeneratorSections X L U.unop at s
      let : Module ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U : Type u)
          (L.val.obj U : Type u) :=
        (L.val.obj U).isModule
      apply Subtype.ext
      change (1 : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U : Type u)) • s.val = s.val
      simp
    mul_act := by
      intro U a b s
      change Multiplicative (Additive ((X.O.obj.obj U : Type u)ˣ)) at a b
      change GeneratorSections X L U.unop at s
      let : Module ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U : Type u)
          (L.val.obj U : Type u) :=
        (L.val.obj U).isModule
      apply Subtype.ext
      let ua : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U : Type u)ˣ :=
        Additive.toMul (Multiplicative.toAdd a)
      let ub : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U : Type u)ˣ :=
        Additive.toMul (Multiplicative.toAdd b)
      let uab : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U : Type u)ˣ :=
        Additive.toMul (Multiplicative.toAdd (a * b))
      change uab.val • s.val = ua.val • (ub.val • s.val)
      have hab : uab = ua * ub := rfl
      rw [hab, Units.val_mul, mul_smul]
    naturality := by
      intro U V f a s
      change Multiplicative (Additive ((X.O.obj.obj U : Type u)ˣ)) at a
      change GeneratorSections X L U.unop at s
      let : Module ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U : Type u)
          (L.val.obj U : Type u) :=
        (L.val.obj U).isModule
      let : Module ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj V : Type u)
          (L.val.obj V : Type u) :=
        (L.val.obj V).isModule
      let ua : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U : Type u)ˣ :=
        Additive.toMul (Multiplicative.toAdd a)
      let uaV : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj V : Type u)ˣ :=
        Units.map
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map f.unop.op).hom.toMonoidHom ua
      apply Subtype.ext
      change (L.val.restrictₛₗ f.unop.op) (ua.val • s.val) =
        uaV.val • (L.val.restrictₛₗ f.unop.op s.val)
      rw [(L.val.restrictₛₗ f.unop.op).map_smulₛₗ]
      congr 1
    simplyTransitive := by
      intro U _ s t
      change GeneratorSections X L U.unop at s t
      let : Module ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U : Type u)
          (L.val.obj U : Type u) :=
        (L.val.obj U).isModule
      obtain ⟨a, ha, huniq⟩ := existsUnique_unit_smul_generatorSections X L U.unop s t
      let E :
          G.presheaf.obj U ≃ ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U : Type u)ˣ := {
        toFun := fun b => Additive.toMul (Multiplicative.toAdd b)
        invFun := fun b => Multiplicative.ofAdd (Additive.ofMul b)
        left_inv := fun b => rfl
        right_inv := fun b => rfl }
      refine ⟨E.symm a, ?_, ?_⟩
      · apply Subtype.ext
        change (E (E.symm a)).val • s.val = t.val
        rw [E.apply_symm_apply]
        exact ha
      · intro b hb
        have hval : E b = a := huniq (E b) (by
          change generatorSections_smul_unit X L U.unop (E b) s = t at hb
          change (E b).val • s.val = t.val
          exact congrArg Subtype.val hb)
        calc
          b = E.symm (E b) := (E.symm_apply_apply b).symm
          _ = E.symm a := congrArg E.symm hval
  }
  have hF : F.IsTorsor := by
    intro U
    obtain ⟨I, V, f, hcover, hgen⟩ := exists_cover_generatorSections X hX L hL U
    refine ⟨Sieve.ofArrows V f, hcover, ?_⟩
    intro W g hg
    obtain ⟨i, k, hk⟩ := Sieve.ofArrows.exists hg
    obtain ⟨s⟩ := hgen i
    exact ⟨generatorSections_restrict X L k s⟩
  refine ⟨⟨F, hF⟩, fun U => Equiv.refl _, ?_, ?_⟩
  · intro U V f s
    rfl
  · intro U a s
    rfl

/-! ### Trivialization from a generator, and isomorphisms of torsors -/

/-- The morphism out of the unit module determined by a section of a module on a slice site
acts by multiplication by that section. -/
theorem unitHomEquiv_symm_app_smul (X : RingedSite.{u, u, u})
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (U : X.C)
    (sec : (L.over U).val.sections)
    (V : (Over U)ᵒᵖ) (r : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U).obj.obj V) :
    (((L.over U).unitHomEquiv.symm sec).val.app V).hom r = r • sec.eval V := by
  rw [unitHom_symm_app_smul (X.J.over U) (L.over U) sec V r]
  simp [LinearMap.ringLmapEquivSelf]

/-- The morphism from the unit module to a module on the slice site over `U` determined by a
local generator over `U`. -/
def generatorUnitHom (X : RingedSite.{u, u, u})
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (U : X.C)
    (s : GeneratorSections X L U) :
    SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) ⟶ L.over U :=
  (L.over U).unitHomEquiv.symm (generatorSections_overSections X L U s.val)

/-- The morphism determined by a local generator is an isomorphism over every object of the
slice site, because the generator generates over every arrow. -/
theorem generatorUnitHom_isIso_app (X : RingedSite.{u, u, u})
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (U : X.C)
    (s : GeneratorSections X L U)
    (V : (Over U)ᵒᵖ) : IsIso ((generatorUnitHom X L U s).val.app V) := by
  apply (ConcreteCategory.isIso_iff_bijective _).2
  have he : ⇑((generatorUnitHom X L U s).val.app V).hom =
      (fun r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V.unop.left) =>
        r • L.val.restrictₛₗ V.unop.hom.op s.val) := by
    funext r
    exact unitHomEquiv_symm_app_smul X L U (generatorSections_overSections X L U s.val) V r
  rw [he]
  exact s.property V.unop.left V.unop.hom

/-- A local generator over `U` trivializes the module on the slice site over `U`. -/
def generatorSectionTrivialization (X : RingedSite.{u, u, u})
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (U : X.C)
    (s : GeneratorSections X L U) :
    SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) ≅ L.over U :=
  letI (V : (Over U)ᵒᵖ) : IsIso ((generatorUnitHom X L U s).val.app V) :=
    generatorUnitHom_isIso_app X L U s V
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk
      (M₁ := (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)).val)
      (M₂ := (L.over U).val)
      (fun V => asIso ((generatorUnitHom X L U s).val.app V))
      (fun {_ _} g => (generatorUnitHom X L U s).val.naturality g))

/-- A morphism of pseudo-torsors is bijective on the sections over an object which has one. -/
theorem torsorHom_bijective_of_nonempty
    {D : Type u} [Category.{v} D] {J : GrothendieckTopology D}
    {G : SheafOfGroups.{u} J} {F F' : PseudoTorsor G}
    (e : F.Hom F') (U : Dᵒᵖ) (s₀ : F.presheaf.obj U) :
    Function.Bijective (e.hom.app U) := by
  constructor
  · intro s t h
    obtain ⟨a, ha, _⟩ := F.simplyTransitive U ⟨s⟩ s t
    have hg : F'.act U a (e.hom.app U s) = e.hom.app U s :=
      (e.map_act U a s).symm.trans ((congrArg (fun z => e.hom.app U z) ha).trans h.symm)
    have ha1 : a = 1 := (F'.simplyTransitive U ⟨e.hom.app U s⟩
      (e.hom.app U s) (e.hom.app U s)).unique hg (F'.one_act U _)
    simpa only [ha1, F.one_act] using ha
  · intro t
    obtain ⟨a, ha, _⟩ := F'.simplyTransitive U ⟨e.hom.app U s₀⟩ (e.hom.app U s₀) t
    exact ⟨F.act U a s₀, (e.map_act U a s₀).trans ha⟩

/-- Every morphism out of a torsor is an isomorphism. -/
theorem torsorHom_isIso
    {D : Type u} [Category.{v} D] {J : GrothendieckTopology D}
    {G : SheafOfGroups.{u} J} {F F' : PseudoTorsor G}
    (hF : F.IsTorsor) (e : F.Hom F') : e.IsIso := by
  change IsIso e.hom
  rw [NatTrans.isIso_iff_isIso_app]
  intro U
  apply (ConcreteCategory.isIso_iff_bijective _).2
  obtain ⟨S, hS, hs⟩ := hF U.unop
  exact bijective_of_bijective_on_cover J F.isSheaf F'.isSheaf S hS e.hom (by
    intro V f hf
    obtain ⟨s⟩ := hs hf
    exact torsorHom_bijective_of_nonempty e (op V) s)

/-! ### The module attached to a torsor under the units -/

/-- The unique unit carrying one section of a torsor to another. -/
def torsorUnitBetween (X : RingedSite.{u, u, u})
    (F : Stacks.Cohomology.Torsors.AbelianTorsor (unitsAddSheaf X)) (U : X.Cᵒᵖ)
    (s t : F.1.presheaf.obj U) : (X.O.obj.obj U)ˣ :=
  Additive.toMul (Multiplicative.toAdd (F.1.simplyTransitive U ⟨s⟩ s t).choose)

/-- The defining property of `torsorUnitBetween`. -/
theorem torsorUnitBetween_act (X : RingedSite.{u, u, u})
    (F : Stacks.Cohomology.Torsors.AbelianTorsor (unitsAddSheaf X)) (U : X.Cᵒᵖ)
    (s t : F.1.presheaf.obj U) :
    F.1.act U (Multiplicative.ofAdd (Additive.ofMul (torsorUnitBetween X F U s t))) s = t :=
  (F.1.simplyTransitive U ⟨s⟩ s t).choose_spec.1

/-- `torsorUnitBetween` is the unique unit with that property. -/
theorem torsorUnitBetween_eq (X : RingedSite.{u, u, u})
    (F : Stacks.Cohomology.Torsors.AbelianTorsor (unitsAddSheaf X)) (U : X.Cᵒᵖ)
    (s t : F.1.presheaf.obj U) (a : (X.O.obj.obj U)ˣ)
    (ha : F.1.act U (Multiplicative.ofAdd (Additive.ofMul a)) s = t) :
    torsorUnitBetween X F U s t = a :=
  congrArg (fun b => Additive.toMul (Multiplicative.toAdd b))
    ((F.1.simplyTransitive U ⟨s⟩ s t).choose_spec.2 _ ha).symm

/-- A section is carried to itself by the unit one. -/
theorem torsorUnitBetween_self (X : RingedSite.{u, u, u})
    (F : Stacks.Cohomology.Torsors.AbelianTorsor (unitsAddSheaf X)) (U : X.Cᵒᵖ)
    (s : F.1.presheaf.obj U) : torsorUnitBetween X F U s s = 1 :=
  torsorUnitBetween_eq X F U s s 1 (F.1.one_act U s)

/-- `torsorUnitBetween` is compatible with restriction. -/
theorem torsorUnitBetween_naturality (X : RingedSite.{u, u, u})
    (F : Stacks.Cohomology.Torsors.AbelianTorsor (unitsAddSheaf X))
    {U V : X.Cᵒᵖ} (f : U ⟶ V) (s t : F.1.presheaf.obj U) :
    torsorUnitBetween X F V (F.1.presheaf.map f s) (F.1.presheaf.map f t) =
      Units.map (X.O.obj.map f).hom.toMonoidHom (torsorUnitBetween X F U s t) := by
  apply torsorUnitBetween_eq
  exact (F.1.naturality f _ s).symm.trans
    (congrArg (fun z => F.1.presheaf.map f z) (torsorUnitBetween_act X F U s t))

/-- Translating the source divides `torsorUnitBetween` by the translating unit. -/
theorem torsorUnitBetween_act_left (X : RingedSite.{u, u, u})
    (F : Stacks.Cohomology.Torsors.AbelianTorsor (unitsAddSheaf X)) (U : X.Cᵒᵖ)
    (s t : F.1.presheaf.obj U) (a : (X.O.obj.obj U)ˣ) :
    torsorUnitBetween X F U (F.1.act U (Multiplicative.ofAdd (Additive.ofMul a)) s) t =
      a⁻¹ * torsorUnitBetween X F U s t := by
  apply torsorUnitBetween_eq
  have h : Multiplicative.ofAdd (Additive.ofMul (a⁻¹ * torsorUnitBetween X F U s t)) *
      Multiplicative.ofAdd (Additive.ofMul a) =
      Multiplicative.ofAdd (Additive.ofMul (torsorUnitBetween X F U s t)) := by
    change Multiplicative.ofAdd (Additive.ofMul
      ((a⁻¹ * torsorUnitBetween X F U s t) * a)) = _
    congr 2
    simp [mul_comm]
  have h1 := F.1.mul_act U
    (Multiplicative.ofAdd (Additive.ofMul (a⁻¹ * torsorUnitBetween X F U s t)))
    (Multiplicative.ofAdd (Additive.ofMul a)) s
  exact h1.symm.trans
    ((congrArg (fun g => F.1.act U g s) h).trans (torsorUnitBetween_act X F U s t))

/-- Translating the target multiplies `torsorUnitBetween` by the translating unit. -/
theorem torsorUnitBetween_act_right (X : RingedSite.{u, u, u})
    (F : Stacks.Cohomology.Torsors.AbelianTorsor (unitsAddSheaf X)) (U : X.Cᵒᵖ)
    (s t : F.1.presheaf.obj U) (a : (X.O.obj.obj U)ˣ) :
    torsorUnitBetween X F U s (F.1.act U (Multiplicative.ofAdd (Additive.ofMul a)) t) =
      a * torsorUnitBetween X F U s t := by
  apply torsorUnitBetween_eq
  have h0 : Multiplicative.ofAdd (Additive.ofMul (a * torsorUnitBetween X F U s t)) =
      Multiplicative.ofAdd (Additive.ofMul a) *
        Multiplicative.ofAdd (Additive.ofMul (torsorUnitBetween X F U s t)) := rfl
  have h1 := F.1.mul_act U (Multiplicative.ofAdd (Additive.ofMul a))
    (Multiplicative.ofAdd (Additive.ofMul (torsorUnitBetween X F U s t))) s
  exact (congrArg (fun g => F.1.act U g s) h0).trans (h1.trans
    (congrArg (fun z => F.1.act U (Multiplicative.ofAdd (Additive.ofMul a)) z)
      (torsorUnitBetween_act X F U s t)))

/-- Families assigning a section of the structure sheaf to every section of the torsor over an
object of the slice over `U`. -/
abbrev CoefficientFamily (X : RingedSite.{u, u, u})
    (F : Stacks.Cohomology.Torsors.AbelianTorsor (unitsAddSheaf X)) (U : X.C) :=
  ∀ V : Over U, F.1.presheaf.obj (op V.left) → X.O.obj.obj (op V.left)

/-- The module structure on the coefficient families, with scalars restricted along the
structure morphisms of the slice. -/
@[instance_reducible] def coefficientFamilyModule (X : RingedSite.{u, u, u})
    (F : Stacks.Cohomology.Torsors.AbelianTorsor (unitsAddSheaf X)) (U : X.C) :
    Module (X.O.obj.obj (op U)) (CoefficientFamily X F U) :=
  @Pi.module _ _ _ _ _ (fun V =>
    @Pi.module _ _ _ _ _ (fun _ => Module.compHom _ (X.O.obj.map V.hom.op).hom))

attribute [local instance] coefficientFamilyModule

/-- The submodule of coefficient families which are compatible with restriction and
equivariant for the unit action, with the action twisted by inversion. -/
def coefficientSubmodule (X : RingedSite.{u, u, u})
    (F : Stacks.Cohomology.Torsors.AbelianTorsor (unitsAddSheaf X)) (U : X.C) :
    Submodule (X.O.obj.obj (op U)) (CoefficientFamily X F U) where
  carrier := {a | (∀ (V W : Over U) (f : W ⟶ V) (s : F.1.presheaf.obj (op V.left)),
      a W (F.1.presheaf.map f.left.op s) = (X.O.obj.map f.left.op) (a V s)) ∧
    ∀ (V : Over U) (g : (X.O.obj.obj (op V.left))ˣ) (s : F.1.presheaf.obj (op V.left)),
      a V (F.1.act _ (Multiplicative.ofAdd (Additive.ofMul g)) s) =
        (g⁻¹ : (X.O.obj.obj (op V.left))ˣ).val * a V s}
  zero_mem' := ⟨fun V W f s => (map_zero (X.O.obj.map f.left.op).hom).symm,
    fun V g s => (mul_zero _).symm⟩
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    constructor
    · intro V W f s
      change a W _ + b W _ = (X.O.obj.map f.left.op) (a V s + b V s)
      rw [ha, hb, map_add]
    · intro V g s
      change a V _ + b V _ = _ * (a V s + b V s)
      rw [ha', hb', mul_add]
  smul_mem' := by
    rintro r a ⟨ha, ha'⟩
    constructor
    · intro V W f s
      change (X.O.obj.map W.hom.op) r * a W _ =
        (X.O.obj.map f.left.op) ((X.O.obj.map V.hom.op) r * a V s)
      rw [ha, map_mul]
      congr 1
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, Over.w f]
    · intro V g s
      change (X.O.obj.map V.hom.op) r * a V _ = _ * ((X.O.obj.map V.hom.op) r * a V s)
      rw [ha', mul_left_comm]

/-- The sections over `U` of the module attached to a torsor. -/
abbrev CoefficientSection (X : RingedSite.{u, u, u})
    (F : Stacks.Cohomology.Torsors.AbelianTorsor (unitsAddSheaf X)) (U : X.C) :=
  coefficientSubmodule X F U

/-- Restriction of coefficient sections, by composing the slice. -/
def coefficientSectionRestrict (X : RingedSite.{u, u, u})
    (F : Stacks.Cohomology.Torsors.AbelianTorsor (unitsAddSheaf X))
    {U V : X.C} (f : V ⟶ U) (a : CoefficientSection X F U) : CoefficientSection X F V := by
  refine ⟨fun W => a.val ((Over.map f).obj W), ?_, ?_⟩
  · intro W Z g s
    exact a.property.1 _ _ ((Over.map f).map g) s
  · intro W g s
    exact a.property.2 ((Over.map f).obj W) g s

/-- The presheaf of modules attached to a torsor under the units. -/
def coefficientPresheaf (X : RingedSite.{u, u, u})
    (F : Stacks.Cohomology.Torsors.AbelianTorsor (unitsAddSheaf X)) :
    PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj where
  obj U := ModuleCat.of (X.O.obj.obj U) (CoefficientSection X F U.unop)
  map {U V} f := by
    letI : Module (X.O.obj.obj U)
        ((ModuleCat.restrictScalars
            ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map f).hom).obj
          (ModuleCat.of (X.O.obj.obj V) (CoefficientSection X F V.unop))) :=
      inferInstanceAs (Module ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U)
        ((ModuleCat.restrictScalars
            ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map f).hom).obj
          (ModuleCat.of (X.O.obj.obj V) (CoefficientSection X F V.unop))))
    exact ModuleCat.ofHom
      (Y := (ModuleCat.restrictScalars
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map f).hom).obj
        (ModuleCat.of (X.O.obj.obj V) (CoefficientSection X F V.unop))) {
      toFun := coefficientSectionRestrict X F f.unop
      map_add' := fun a b => rfl
      map_smul' := by
        intro r a
        apply Subtype.ext
        funext W s
        change (X.O.obj.map (W.hom ≫ f.unop).op) r * _ =
          (X.O.obj.map W.hom.op) ((X.O.obj.map f) r) * _
        rw [op_comp, X.O.obj.map_comp]
        rfl }
  map_id U := by
    ext a
    apply Subtype.ext
    funext W s
    change a.val ((Over.map (𝟙 U.unop)).obj W) s = a.val W s
    simpa using (a.property.1 _ _ ((Over.mapId U.unop).inv.app W) s).symm
  map_comp {U V W} f g := by
    ext a
    apply Subtype.ext
    funext T s
    change a.val ((Over.map (f ≫ g).unop).obj T) s =
      a.val ((Over.map f.unop).obj ((Over.map g.unop).obj T)) s
    simpa using a.property.1 _ _ ((Over.mapComp g.unop f.unop).hom.app T) s

/-- The equivariant maps from the torsor to the structure sheaf, as a subfunctor of the internal
hom presheaf. -/
def equivariantHomSubfunctor (X : RingedSite.{u, u, u})
    (F : Stacks.Cohomology.Torsors.AbelianTorsor (unitsAddSheaf X)) :
    Subfunctor (presheafHom F.1.presheaf (X.O.obj ⋙ forget CommRingCat)) where
  obj U := {a | ∀ (V : Over U.unop) (g : (X.O.obj.obj (op V.left))ˣ)
      (s : F.1.presheaf.obj (op V.left)),
      a.app (op V) (F.1.act _ (Multiplicative.ofAdd (Additive.ofMul g)) s) =
        @HMul.hMul (X.O.obj.obj (op V.left)) (X.O.obj.obj (op V.left))
          (X.O.obj.obj (op V.left)) inferInstance (g⁻¹).val (a.app (op V) s)}
  map := by
    intro U V f a ha W g s
    exact ha ((Over.map f.unop).obj W) g s

/-- The presheaf of modules attached to a torsor is the subfunctor of equivariant maps. -/
def coefficientPresheafIso (X : RingedSite.{u, u, u})
    (F : Stacks.Cohomology.Torsors.AbelianTorsor (unitsAddSheaf X)) :
    (coefficientPresheaf X F).presheaf ⋙ forget AddCommGrpCat ≅
      (equivariantHomSubfunctor X F).toFunctor :=
  NatIso.ofComponents (fun U => Equiv.toIso {
    toFun := fun a => ⟨{
      app := fun V => ↾(a.val V.unop)
      naturality := by
        intro V W f
        ext s
        exact a.property.1 V.unop W.unop f.unop s }, a.property.2⟩
    invFun := fun a => ⟨fun V s => a.val.app (op V) s,
      (fun V W f s => NatTrans.naturality_apply a.val f.op s), a.property⟩
    left_inv := fun a => rfl
    right_inv := fun a => rfl }) (by intros; rfl)

/-- The equivariant maps from a torsor to the structure sheaf form a sheaf. -/
theorem equivariantHomSubfunctor_isSheaf (X : RingedSite.{u, u, u})
    (F : Stacks.Cohomology.Torsors.AbelianTorsor (unitsAddSheaf X)) :
    Presheaf.IsSheaf X.J (equivariantHomSubfunctor X F).toFunctor := by
  let R := X.O.obj ⋙ forget CommRingCat
  have hR : Presheaf.IsSheaf X.J R :=
    Presheaf.isSheaf_comp_of_isSheaf X.J _ _ X.O.property
  have hHom := Presheaf.IsSheaf.hom F.1.presheaf R hR
  apply (isSheaf_iff_isSheaf_of_type X.J _).2
  rw [Subfunctor.isSheaf_iff (G := equivariantHomSubfunctor X F)
    ((isSheaf_iff_isSheaf_of_type X.J _).1 hHom)]
  intro U a ha V g s
  let S := (equivariantHomSubfunctor X F).sieveOfSection a
  apply (hR.isSheafFor (S.pullback V.hom) (X.J.pullback_stable _ ha)).isSeparatedFor.ext
  intro W f hf
  let gW : (X.O.obj.obj (op W))ˣ := Units.map (X.O.obj.map f.op).hom.toMonoidHom g
  have hnat (t : F.1.presheaf.obj (op V.left)) :
      a.app (op (Over.mk (f ≫ V.hom))) (F.1.presheaf.map f.op t) =
        R.map f.op (a.app (op V) t) :=
    NatTrans.naturality_apply a (Over.homMk f : Over.mk (f ≫ V.hom) ⟶ V).op t
  have hres : ((presheafHom F.1.presheaf R).map (f ≫ V.hom).op a).app (op (Over.mk (𝟙 W))) =
      a.app (op (Over.mk (f ≫ V.hom))) :=
    presheafHom_map_app (𝟙 W) (f ≫ V.hom) (f ≫ V.hom) (by simp) a
  have hlocal := hf (Over.mk (𝟙 W)) gW (F.1.presheaf.map f.op s)
  rw [hres] at hlocal
  have hact : F.1.presheaf.map f.op
      (F.1.act (op V.left) (Multiplicative.ofAdd (Additive.ofMul g)) s) =
      F.1.act (op W) (Multiplicative.ofAdd (Additive.ofMul gW))
        (F.1.presheaf.map f.op s) := F.1.naturality f.op _ s
  have hgW : (gW⁻¹ : (X.O.obj.obj (op W))ˣ).val =
      R.map f.op (g⁻¹ : (X.O.obj.obj (op V.left))ˣ).val := rfl
  calc R.map f.op (a.app (op V)
          (F.1.act (op V.left) (Multiplicative.ofAdd (Additive.ofMul g)) s))
      = a.app (op (Over.mk (f ≫ V.hom))) (F.1.presheaf.map f.op
          (F.1.act (op V.left) (Multiplicative.ofAdd (Additive.ofMul g)) s)) := (hnat _).symm
    _ = a.app (op (Over.mk (f ≫ V.hom)))
          (F.1.act (op W) (Multiplicative.ofAdd (Additive.ofMul gW))
            (F.1.presheaf.map f.op s)) := congrArg _ hact
    _ = @HMul.hMul (X.O.obj.obj (op W)) (X.O.obj.obj (op W)) (X.O.obj.obj (op W))
          inferInstance (gW⁻¹).val
          (a.app (op (Over.mk (f ≫ V.hom))) (F.1.presheaf.map f.op s)) := hlocal
    _ = @HMul.hMul (X.O.obj.obj (op W)) (X.O.obj.obj (op W)) (X.O.obj.obj (op W))
          inferInstance (R.map f.op (g⁻¹ : (X.O.obj.obj (op V.left))ˣ).val)
          (R.map f.op (a.app (op V) s)) := by rw [hgW, hnat s]
    _ = R.map f.op (@HMul.hMul (X.O.obj.obj (op V.left)) (X.O.obj.obj (op V.left))
          (X.O.obj.obj (op V.left)) inferInstance (g⁻¹).val (a.app (op V) s)) :=
        (map_mul (X.O.obj.map f.op).hom _ _).symm

/-- The sheaf of modules attached to a torsor under the units. -/
def coefficientSheaf (X : RingedSite.{u, u, u})
    (F : Stacks.Cohomology.Torsors.AbelianTorsor (unitsAddSheaf X)) :
    SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf X.O) := by
  refine ⟨coefficientPresheaf X F, ?_⟩
  apply (Presheaf.isSheaf_iff_isSheaf_comp X.J (coefficientPresheaf X F).presheaf
    (forget AddCommGrpCat)).2
  exact (Presheaf.isSheaf_of_iso_iff (coefficientPresheafIso X F)).2
    (equivariantHomSubfunctor_isSheaf X F)

/-- Restriction in the sheaf attached to a torsor is restriction of coefficient sections. -/
theorem coefficientSheaf_restrict (X : RingedSite.{u, u, u})
    (F : Stacks.Cohomology.Torsors.AbelianTorsor (unitsAddSheaf X))
    {U V : X.C} (f : V ⟶ U) (a : CoefficientSection X F U) :
    (coefficientSheaf X F).val.restrictₛₗ f.op a = coefficientSectionRestrict X F f a := rfl

/-- A section of the torsor over `U` gives a coefficient section over `U`: the unit carrying a
given section to the restriction of the chosen one. -/
def coefficientGenerator (X : RingedSite.{u, u, u})
    (F : Stacks.Cohomology.Torsors.AbelianTorsor (unitsAddSheaf X)) (U : X.C)
    (s : F.1.presheaf.obj (op U)) : CoefficientSection X F U := by
  refine ⟨fun V t => (torsorUnitBetween X F (op V.left) t (F.1.presheaf.map V.hom.op s)).val,
    ?_, ?_⟩
  · intro V W f t
    have h : F.1.presheaf.map f.left.op (F.1.presheaf.map V.hom.op s) =
        F.1.presheaf.map W.hom.op s := by
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, Over.w f]
    change (torsorUnitBetween X F (op W.left) (F.1.presheaf.map f.left.op t)
      (F.1.presheaf.map W.hom.op s)).val = _
    calc
      _ = (torsorUnitBetween X F (op W.left) (F.1.presheaf.map f.left.op t)
          (F.1.presheaf.map f.left.op (F.1.presheaf.map V.hom.op s))).val :=
        congrArg (fun z => (torsorUnitBetween X F (op W.left)
          (F.1.presheaf.map f.left.op t) z).val) h.symm
      _ = _ := congrArg Units.val
        (torsorUnitBetween_naturality X F f.left.op t (F.1.presheaf.map V.hom.op s))
  · intro V g t
    exact congrArg Units.val
      (torsorUnitBetween_act_left X F (op V.left) t (F.1.presheaf.map V.hom.op s) g)

/-- `coefficientGenerator` is compatible with restriction. -/
theorem coefficientGenerator_restrict (X : RingedSite.{u, u, u})
    (F : Stacks.Cohomology.Torsors.AbelianTorsor (unitsAddSheaf X))
    {U V : X.C} (f : V ⟶ U) (s : F.1.presheaf.obj (op U)) :
    coefficientSectionRestrict X F f (coefficientGenerator X F U s) =
      coefficientGenerator X F V (F.1.presheaf.map f.op s) := by
  apply Subtype.ext
  funext W t
  change (torsorUnitBetween X F _ t (F.1.presheaf.map (W.hom ≫ f).op s)).val =
    (torsorUnitBetween X F _ t (F.1.presheaf.map W.hom.op (F.1.presheaf.map f.op s))).val
  rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

/-- Every coefficient section is a multiple of the one attached to a section of the torsor. -/
theorem coefficientSection_eq_smul_generator (X : RingedSite.{u, u, u})
    (F : Stacks.Cohomology.Torsors.AbelianTorsor (unitsAddSheaf X)) (U : X.C)
    (s : F.1.presheaf.obj (op U)) (a : CoefficientSection X F U) :
    a = a.val (Over.mk (𝟙 U)) s • coefficientGenerator X F U s := by
  apply Subtype.ext
  funext V t
  let sV := F.1.presheaf.map V.hom.op s
  let q := torsorUnitBetween X F (op V.left) t sV
  have he := a.property.2 V q t
  rw [torsorUnitBetween_act] at he
  have hn := a.property.1 (Over.mk (𝟙 U)) V (Over.homMk V.hom) s
  change a.val V sV = (X.O.obj.map V.hom.op) (a.val (Over.mk (𝟙 U)) s) at hn
  change a.val V t = (X.O.obj.map V.hom.op) (a.val (Over.mk (𝟙 U)) s) * q.val
  calc
    a.val V t = q.val * ((q⁻¹).val * a.val V t) := by simp
    _ = q.val * a.val V sV := congrArg (q.val * ·) he.symm
    _ = q.val * (X.O.obj.map V.hom.op) (a.val (Over.mk (𝟙 U)) s) := by rw [hn]
    _ = _ := mul_comm _ _

/-- Multiplication by the coefficient section attached to a section of the torsor is
bijective. -/
theorem coefficientGenerator_bijective (X : RingedSite.{u, u, u})
    (F : Stacks.Cohomology.Torsors.AbelianTorsor (unitsAddSheaf X)) (U : X.C)
    (s : F.1.presheaf.obj (op U)) :
    Function.Bijective (fun r : X.O.obj.obj (op U) => r • coefficientGenerator X F U s) := by
  constructor
  · intro r t h
    have he := congrArg (fun a : CoefficientSection X F U => a.val (Over.mk (𝟙 U)) s) h
    change (X.O.obj.map (𝟙 U).op) r *
        (torsorUnitBetween X F (op U) s (F.1.presheaf.map (𝟙 U).op s)).val =
      (X.O.obj.map (𝟙 U).op) t *
        (torsorUnitBetween X F (op U) s (F.1.presheaf.map (𝟙 U).op s)).val at he
    simpa [torsorUnitBetween_self] using he
  · intro a
    exact ⟨a.val (Over.mk (𝟙 U)) s, (coefficientSection_eq_smul_generator X F U s a).symm⟩

/-- The coefficient section attached to a section of the torsor is a local generator. -/
def coefficientGeneratorSections (X : RingedSite.{u, u, u})
    (F : Stacks.Cohomology.Torsors.AbelianTorsor (unitsAddSheaf X)) (U : X.C)
    (s : F.1.presheaf.obj (op U)) : GeneratorSections X (coefficientSheaf X F) U := by
  refine ⟨coefficientGenerator X F U s, ?_⟩
  intro V f
  have h : (coefficientSheaf X F).val.restrictₛₗ f.op (coefficientGenerator X F U s) =
      coefficientGenerator X F V (F.1.presheaf.map f.op s) :=
    (coefficientSheaf_restrict X F f _).trans (coefficientGenerator_restrict X F f s)
  rw [h]
  exact coefficientGenerator_bijective X F V (F.1.presheaf.map f.op s)

/-- The module attached to a torsor under the units is invertible: it is locally free of rank
one, because a section of the torsor trivializes it. -/
theorem coefficientSheaf_isInvertible (X : RingedSite.{u, u, u})
    (F : Stacks.Cohomology.Torsors.AbelianTorsor (unitsAddSheaf X)) :
    Stacks.SheafOfModules.IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2
      (coefficientSheaf X F) := by
  apply AlgebraicGeometry.RingedSite.isInvertible_of_isFiniteLocallyFreeOfRank_one
  intro U
  obtain ⟨S, hS, hF⟩ := F.property U
  obtain ⟨I, V, f, rfl⟩ := S.exists_eq_ofArrows
  refine ⟨I, V, f, hS, ?_⟩
  intro i
  obtain ⟨s⟩ := hF (Sieve.ofArrows_mk V f i)
  let e := generatorSectionTrivialization X (coefficientSheaf X F) (V i)
    (coefficientGeneratorSections X F (V i) s)
  exact ⟨(fun _ => e.hom), ⟨cofanFinOneIsColimitOfIso e⟩⟩

/-- The map from a torsor to the generator torsor of its attached module. -/
def coefficientGeneratorTorsorHom (X : RingedSite.{u, u, u})
    (hX : AlgebraicGeometry.RingedSite.IsLocallyRinged X)
    (F : Stacks.Cohomology.Torsors.AbelianTorsor (unitsAddSheaf X)) :
    F.val.Hom (generatorTorsor X hX (coefficientSheaf X F)
      (coefficientSheaf_isInvertible X F)).torsor.val where
  hom := {
    app := fun U => ↾(coefficientGeneratorSections X F U.unop)
    naturality := by
      intro U V f
      ext s
      apply Subtype.ext
      exact ((coefficientSheaf_restrict X F f.unop
        (coefficientGenerator X F U.unop s)).trans
          (coefficientGenerator_restrict X F f.unop s)).symm }
  map_act := by
    intro U a s
    apply Subtype.ext
    apply Subtype.ext
    funext V t
    change (torsorUnitBetween X F (op V.left) t
        (F.1.presheaf.map V.hom.op (F.1.act U a s))).val =
      (X.O.obj.map V.hom.op) (Additive.toMul (Multiplicative.toAdd a)).val *
        (torsorUnitBetween X F (op V.left) t (F.1.presheaf.map V.hom.op s)).val
    rw [F.1.naturality]
    exact congrArg Units.val (torsorUnitBetween_act_right X F (op V.left) t
      (F.1.presheaf.map V.hom.op s)
      (Units.map (X.O.obj.map V.hom.op).hom.toMonoidHom
        (Additive.toMul (Multiplicative.toAdd a))))

/-- **Every torsor under the units is a generator torsor.** A torsor is isomorphic to the
generator torsor of the invertible module attached to it. -/
theorem coefficientGeneratorTorsor_isIsomorphic (X : RingedSite.{u, u, u})
    (hX : AlgebraicGeometry.RingedSite.IsLocallyRinged X)
    (F : Stacks.Cohomology.Torsors.AbelianTorsor (unitsAddSheaf X)) :
    Stacks.Cohomology.Torsors.AbelianTorsor.IsIsomorphic F
      (generatorTorsor X hX (coefficientSheaf X F) (coefficientSheaf_isInvertible X F)).torsor :=
  ⟨coefficientGeneratorTorsorHom X hX F,
    torsorHom_isIso F.property (coefficientGeneratorTorsorHom X hX F)⟩

/-! ### Isomorphisms of modules and of generator torsors -/

/-- Multiplication by the image of a section under an isomorphism is bijective exactly when
multiplication by the section is. -/
theorem generatorMap_bijective_iff
    (X : RingedSite.{u, u, u})
    {L N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (e : L ≅ N)
    (U : X.C) (s : L.val.obj (op U)) :
    Function.Bijective (fun r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U) =>
      r • (e.hom.val.app (op U)).hom s) ↔
    Function.Bijective
      (fun r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U) => r • s) := by
  let α := (e.hom.val.app (op U)).hom
  have hcomp : IsIso (e.hom.val.app (op U)) :=
    Functor.map_isIso
      (SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)) e.hom
  have hα : Function.Bijective α := (ConcreteCategory.isIso_iff_bijective _).mp hcomp
  have hfun : (fun r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U) => r • α s) =
      α ∘ (fun r => r • s) := by
    funext r
    exact (α.map_smul r s).symm
  rw [hfun]
  exact hα.of_comp_iff' _

/-- A module isomorphism takes a local generator to a local generator. -/
def generatorSections_mapIso
    (X : RingedSite.{u, u, u})
    {L N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (e : L ≅ N)
    (U : X.C) (s : GeneratorSections X L U) : GeneratorSections X N U := by
  refine ⟨(e.hom.val.app (op U)).hom s.val, ?_⟩
  intro V f
  let α := (e.hom.val.app (op V)).hom
  have hgen := s.property V f
  have hnat := PresheafOfModules.naturality_apply e.hom.val f.op s.val
  have heq : N.val.restrictₛₗ f.op ((e.hom.val.app (op U)).hom s.val) =
      α (L.val.restrictₛₗ f.op s.val) := by
    simpa only [PresheafOfModules.restrictₛₗ_apply] using hnat.symm
  simpa only [heq] using
    (generatorMap_bijective_iff X e V (L.val.restrictₛₗ f.op s.val)).2 hgen

/-- Transporting a local generator along an isomorphism commutes with restriction. -/
theorem generatorSections_mapIso_restrict
    (X : RingedSite.{u, u, u})
    {L N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (e : L ≅ N)
    {U V : X.C} (f : V ⟶ U) (s : GeneratorSections X L U) :
    generatorSections_mapIso X e V (generatorSections_restrict X L f s) =
      generatorSections_restrict X N f (generatorSections_mapIso X e U s) := by
  apply Subtype.ext
  simpa [generatorSections_mapIso, generatorSections_restrict,
    PresheafOfModules.restrictₛₗ_apply] using
    PresheafOfModules.naturality_apply e.hom.val f.op s.val

/-- Transporting a local generator along an isomorphism is a bijection. -/
theorem generatorSections_mapIso_bijective
    (X : RingedSite.{u, u, u})
    {L N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (e : L ≅ N)
    (U : X.C) : Function.Bijective (generatorSections_mapIso X e U) := by
  constructor
  · intro s t h
    apply Subtype.ext
    have hc : IsIso (e.hom.val.app (op U)) :=
      Functor.map_isIso
        (SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)) e.hom
    exact (ConcreteCategory.isIso_iff_bijective _).mp hc |>.1 (congrArg Subtype.val h)
  · intro t
    refine ⟨generatorSections_mapIso X e.symm U t, ?_⟩
    apply Subtype.ext
    change (e.hom.val.app (op U)).hom ((e.inv.val.app (op U)).hom t.val) = t.val
    have hcomp' : e.inv.val.app (op U) ≫ e.hom.val.app (op U) = 𝟙 _ := by
      simpa only [SheafOfModules.comp_val, SheafOfModules.id_val,
        PresheafOfModules.comp_app, PresheafOfModules.id_app] using
        congrArg (fun g : N ⟶ N => g.val.app (op U)) e.inv_hom_id
    exact congrArg (fun f => f.hom t.val) hcomp'

/-- The map on sections induced by an isomorphism of modules: transport the corresponding local
generator. -/
def generatorTorsorMapOfIso
    (X : RingedSite.{u, u, u})
    {L N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (e : L ≅ N)
    (F : GeneratorTorsor X L) (G : GeneratorTorsor X N) (U : X.Cᵒᵖ)
    (s : F.torsor.1.presheaf.obj U) : G.torsor.1.presheaf.obj U :=
  (G.sectionsEquiv U).symm (generatorSections_mapIso X e U.unop (F.sectionsEquiv U s))

/-- The module section underlying the transported generator is the image of the original one. -/
private theorem sectionsEquiv_generatorTorsorMapOfIso_val
    (X : RingedSite.{u, u, u})
    {L N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (e : L ≅ N)
    (F : GeneratorTorsor X L) (G : GeneratorTorsor X N) (U : X.Cᵒᵖ)
    (s : F.torsor.1.presheaf.obj U) :
    (G.sectionsEquiv U (generatorTorsorMapOfIso X e F G U s)).val =
      (e.hom.val.app U).hom (F.sectionsEquiv U s).val :=
  congrArg Subtype.val (Equiv.apply_symm_apply _ _)

/-- The induced map on sections is compatible with restriction. -/
theorem generatorTorsorMapOfIso_restrict
    (X : RingedSite.{u, u, u})
    {L N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (e : L ≅ N)
    (F : GeneratorTorsor X L) (G : GeneratorTorsor X N) {U V : X.Cᵒᵖ} (f : U ⟶ V)
    (s : F.torsor.1.presheaf.obj U) :
    generatorTorsorMapOfIso X e F G V (F.torsor.1.presheaf.map f s) =
      G.torsor.1.presheaf.map f (generatorTorsorMapOfIso X e F G U s) := by
  apply (G.sectionsEquiv V).injective
  apply Subtype.ext
  rw [sectionsEquiv_generatorTorsorMapOfIso_val, G.sectionsEquiv_restrict,
    sectionsEquiv_generatorTorsorMapOfIso_val, F.sectionsEquiv_restrict]
  exact PresheafOfModules.naturality_apply e.hom.val f (F.sectionsEquiv U s).val

/-- The induced map on sections is equivariant for the action of the units. -/
theorem generatorTorsorMapOfIso_act
    (X : RingedSite.{u, u, u})
    {L N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (e : L ≅ N)
    (F : GeneratorTorsor X L) (G : GeneratorTorsor X N) (U : X.Cᵒᵖ)
    (a : (Stacks.Cohomology.Torsors.abelianSheafAsGroupSheaf (unitsAddSheaf X)).presheaf.obj U)
    (s : F.torsor.1.presheaf.obj U) :
    generatorTorsorMapOfIso X e F G U (F.torsor.1.act U a s) =
      G.torsor.1.act U a (generatorTorsorMapOfIso X e F G U s) := by
  let : Module (X.O.obj.obj U) (L.val.obj U) := (L.val.obj U).isModule
  let : Module (X.O.obj.obj U) (N.val.obj U) := (N.val.obj U).isModule
  apply (G.sectionsEquiv U).injective
  apply Subtype.ext
  let b : (X.O.obj.obj U)ˣ := Additive.toMul (Multiplicative.toAdd a)
  have hF := F.sectionsEquiv_smul U b s
  have hG := G.sectionsEquiv_smul U b (generatorTorsorMapOfIso X e F G U s)
  rw [sectionsEquiv_generatorTorsorMapOfIso_val] at hG
  rw [sectionsEquiv_generatorTorsorMapOfIso_val]
  exact (congrArg _ hF).trans (((e.hom.val.app U).hom.map_smul b.val _).trans hG.symm)

/-- The morphism of torsors induced by an isomorphism of modules. -/
def generatorTorsorHomOfIso
    (X : RingedSite.{u, u, u})
    {L N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (e : L ≅ N)
    (F : GeneratorTorsor X L) (G : GeneratorTorsor X N) : F.torsor.1.Hom G.torsor.1 where
  hom := {
    app := fun U => ↾(generatorTorsorMapOfIso X e F G U)
    naturality := by
      intro U V f
      ext s
      exact generatorTorsorMapOfIso_restrict X e F G f s }
  map_act := generatorTorsorMapOfIso_act X e F G

/-- **Isomorphic modules have isomorphic generator torsors.** -/
theorem generatorTorsor_isIsomorphic_of_iso
    (X : RingedSite.{u, u, u})
    {L N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (e : L ≅ N)
    (F : GeneratorTorsor X L) (G : GeneratorTorsor X N) :
    Stacks.Cohomology.Torsors.AbelianTorsor.IsIsomorphic F.torsor G.torsor := by
  refine ⟨generatorTorsorHomOfIso X e F G, ?_⟩
  change IsIso (generatorTorsorHomOfIso X e F G).hom
  rw [NatTrans.isIso_iff_isIso_app]
  intro U
  apply (ConcreteCategory.isIso_iff_bijective _).2
  have h : Function.Bijective (generatorTorsorMapOfIso X e F G U) :=
    (G.sectionsEquiv U).symm.bijective.comp
      ((generatorSections_mapIso_bijective X e U.unop).comp (F.sectionsEquiv U).bijective)
  exact h

end Stacks.Cohomology.Torsors.Generators

end
