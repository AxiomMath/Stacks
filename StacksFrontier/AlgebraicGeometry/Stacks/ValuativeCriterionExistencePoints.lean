module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.Valuative.ExistenceSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Representability
public import StacksFrontier.AlgebraicGeometry.Stacks.ValuativeCriterionDottedSpan
public import StacksFrontier.AlgebraicGeometry.Stacks.ValuativeCriterionProductPoint

/-!
# Valuative existence is tested on the algebraic-space base changes (Stacks 0CLN)

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over a scheme `S` of a big fppf site which is
representable by algebraic spaces (Stacks 02ZW). Then `f` satisfies the existence part of the
valuative criterion (Stacks 0CLK) exactly when every one of its base changes to an algebraic space
does, in the sense of Stacks 03IX: for every object `U` of the site, every scheme-valued point `y`
of `𝒴` over `U` and every algebraic space `F` over `U` representing the first projection of the
2-fibre product `U ×_𝒴 𝒳`, the structure morphism of `F` satisfies the existence criterion for
presheaves.

## Main definitions

* `AlgebraicGeometry.Stack.dominatingExtensionOfRingMaps`: a dominating extension of a valuative
  square built from a dominating extension of its valuation ring.
* `AlgebraicGeometry.Stack.presheafSquareOfStack`: the valuative square for the representing
  presheaf attached to a valuative square for `f`.

## Main results

* `AlgebraicGeometry.Stack.valuativeCriterionExistence_iff_baseChange`: **Stacks 0CLN**.
* `AlgebraicGeometry.Stack.valuativeCriterionExistence_baseChange_point` and
  `AlgebraicGeometry.Stack.valuativeCriterionExistence_of_baseChange`: its two directions, usable
  separately. The forward one needs no representability hypothesis; its name carries `point`
  because the base change it passes to is one along a scheme-valued point of the target, where
  `AlgebraicGeometry.Stack.valuativeCriterionExistence_baseChange` is the base change along a
  1-morphism of algebraic stacks.
* `AlgebraicGeometry.Stack.nonempty_lift_baseChange_point`: the forward direction strengthened so
  that the dotted arrow lives over the *given* valuation ring rather than over a dominating
  extension of it, from the correspondingly strengthened hypothesis on the valuative squares of
  `f` whose valuation ring satisfies a prescribed predicate.

## Implementation notes

The statement is the one of Stacks 0CLJ
(`AlgebraicGeometry.Stack.valuativeCriterionUniqueness_iff_baseChange`) with uniqueness replaced
by existence, and the proof runs through the same dictionary, but at a single object rather than
at a whole section: the existence criterion asserts that *one* dotted arrow exists, and a dotted
arrow is determined by its value at the unit object of the slice.

Concretely both directions pass through a *span* in `𝒳` compatible with the link of the valuative
square, as in `StacksFrontier/AlgebraicGeometry/Stacks/ValuativeCriterionDottedSpan.lean`:

* *From the stack to the base change.* A valuative square `q` for the presheaf `F` lifts to a
  valuative square `Q` for `f` over the base `S`, by naming the generic point of `q` with an object
  of the 2-fibre product (`CategoryTheory.TwoFibreProductOver.exists_mk_of_section`), carrying that
  object and the value of the point `y` to 1-morphisms out of slices
  (`CategoryTheory.Functor.TwoYoneda.exists_basedFunctor_unitHom`) and filling the square with the
  2-Yoneda extension of the comparison morphism
  (`CategoryTheory.Functor.TwoYoneda.homOverBase`), whose component at the unit object is by
  construction the link of `Q`. A dotted arrow for `Q` gives a span, and a span gives a section of
  `F` over the spectrum of the extended valuation ring
  (`CategoryTheory.TwoFibreProductOver.exists_section_of_span`), which is a dotted arrow for `q`
  (`AlgebraicGeometry.Space.ValuativeSquare.liftOfSection`).

* *From the base change to the stack.* A valuative square `q` for `f` has a base change along its
  own special point, and the generic point of `q` names a section of the representing presheaf
  (`AlgebraicGeometry.Stack.genericProductPoint`); together with the terminal structure morphism
  this is a valuative square for the presheaf. A dotted arrow for it names a second section, the
  two sections are related by morphisms of the 2-fibre product
  (`CategoryTheory.PresheafOfCategories.exists_hom_of_sectionOfObj_map`), and the `𝒳`-components of
  those morphisms are the span, compatible with the link by
  `AlgebraicGeometry.Stack.productPointLink_map`.

The structure morphism of the presheaf is the unique one to the representable terminal presheaf
`AlgebraicGeometry.Space.isTerminal_yoneda_obj_base`, so every commutation condition involving it
holds by terminality and none has to be checked.

## References

* [Stacks Project, Tag 0CLN](https://stacks.math.columbia.edu/tag/0CLN)
* [Stacks Project, Tag 0CLK](https://stacks.math.columbia.edu/tag/0CLK)
* [Stacks Project, Tag 02ZW](https://stacks.math.columbia.edu/tag/02ZW)
* [Stacks Project, Tag 03IX](https://stacks.math.columbia.edu/tag/03IX)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.PresheafOfCategories Opposite

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor
  CategoryTheory.BasedFunctor.comp CategoryTheory.Bicategory.InducedBicategory
  CategoryTheory.TwoFibreProductOver.fst AlgebraicGeometry.Stack.sitePointOfSchemePoint

namespace AlgebraicGeometry.Stack

universe u w

section Auxiliary

variable (B : BigFppfSite.{u}) {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- **A dominating extension of a valuative square from a dominating extension of rings.** All the
morphisms of site objects and the 1-morphisms of categories fibred in groupoids are the canonical
ones, so every `_canonical` field holds by `rfl` and the filling 2-morphism of the square of
spectra is an `eqToHom`. -/
noncomputable def dominatingExtensionOfRingMaps {f : 𝒳 ⟶ 𝒴} (q : ValuativeSquare B S hS f)
    (R' K' : Type u) [CommRing R'] [IsDomain R'] [ValuationRing R']
    [Field K'] [Algebra R' K'] [IsFractionRing R' K']
    (a : q.R →+* R') (k : q.K →+* K') (ha : IsLocalHom a)
    (hk : (algebraMap R' K').comp a = k.comp (algebraMap q.R q.K))
    (hR' : B.Contains (Spec (.of R'))) (hK' : B.Contains (Spec (.of K'))) :
    q.DominatingExtension := by
  have hc : Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫
      Spec.map (CommRingCat.ofHom a) =
      Spec.map (CommRingCat.ofHom k) ≫
        Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun t => Spec.map (CommRingCat.ofHom t)) hk
  let ao : siteObject B S hS hR' (Spec.map (CommRingCat.ofHom a) ≫ q.base) ⟶
      siteObject B S hS q.ring_mem q.base :=
    Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom a)))
  let jo : siteObject B S hS hK' (Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫
        Spec.map (CommRingCat.ofHom a) ≫ q.base) ⟶
      siteObject B S hS hR' (Spec.map (CommRingCat.ofHom a) ≫ q.base) :=
    Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap R' K'))))
  let ko : siteObject B S hS hK' (Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫
        Spec.map (CommRingCat.ofHom a) ≫ q.base) ⟶
      siteObject B S hS q.field_mem
        (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base) :=
    Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom k))) (by
      apply ObjectProperty.hom_ext
      change Spec.map (CommRingCat.ofHom k) ≫
        (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base) = _
      rw [← Category.assoc, ← hc, Category.assoc]
      rfl)
  have hc' : jo ≫ ao = ko ≫ q.genericMap := by
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    change Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫
      Spec.map (CommRingCat.ofHom a) =
      Spec.map (CommRingCat.ofHom k) ≫ B.inclusion.map q.genericMap.left
    rw [q.genericMap_left]
    exact hc
  exact
    { R' := R', K' := K', ringMap := a, fieldMap := k, isLocalHom := ha,
      fraction_comm := hk, ring_mem := hR', field_mem := hK',
      specialOver := ao, specialOver_left := rfl,
      genericOver := ko, genericOver_left := rfl,
      genericMap := jo, genericMap_left := rfl,
      j := schemeMorphism B jo, j_canonical := rfl,
      a := schemeMorphism B ao, a_canonical := rfl,
      k := schemeMorphism B ko, k_canonical := rfl,
      commute := eqToHom (by
        rw [schemeMorphism_eq_of_canonical B q.genericMap q.j q.j_canonical,
          schemeMorphism_comp, schemeMorphism_comp, hc']) }

open CategoryTheory.Bicategory in
/-- **A dotted arrow for a valuative square gives one for any dominating extension of it.** The
diagonal of the extended rectangle is the extension's map of special points followed by the given
diagonal, and the two triangles are the pastings of the square of spectra filling the extension
with the triangles of the given dotted arrow; the compatibility is the exchange law for the
2-morphism filling that square and the lower triangle. -/
private noncomputable def extendDottedArrow {f : 𝒳 ⟶ 𝒴} (q : ValuativeSquare B S hS f)
    (d : q.DominatingExtension) (l : DottedArrow q.x q.j f.hom q.y q.γ) :
    DottedArrow (d.k ≫ q.x) d.j f.hom (d.a ≫ q.y) d.inducedGamma where
  a := d.a ≫ l.a
  α := (α_ d.j d.a l.a).inv ≫ (d.commute ▷ l.a) ≫ (α_ d.k q.j l.a).hom ≫ (d.k ◁ l.α)
  β := (d.a ◁ l.β) ≫ (α_ d.a l.a f.hom).inv
  compat := by
    calc d.inducedGamma
        = (α_ d.j d.a q.y).inv ≫ ((d.commute ▷ q.y) ≫ ((d.k ≫ q.j) ◁ l.β)) ≫
            ((α_ d.k q.j (l.a ≫ f.hom)).hom ≫
              (d.k ◁ ((α_ q.j l.a f.hom).inv ≫ (l.α ▷ f.hom))) ≫
                (α_ d.k q.x f.hom).inv) := by
          simp only [ValuativeSquare.DominatingExtension.inducedGamma, l.compat]
          bicategory
      _ = (α_ d.j d.a q.y).inv ≫ (((d.j ≫ d.a) ◁ l.β) ≫ (d.commute ▷ (l.a ≫ f.hom))) ≫
            ((α_ d.k q.j (l.a ≫ f.hom)).hom ≫
              (d.k ◁ ((α_ q.j l.a f.hom).inv ≫ (l.α ▷ f.hom))) ≫
                (α_ d.k q.x f.hom).inv) := by
          rw [← Bicategory.whisker_exchange]
      _ = _ := by bicategory

/-- **The valuative square for the representing presheaf attached to a valuative square for `f`.**
Its valuation ring is that of `q`, its base morphism is the identity of the spectrum of that ring,
its generic point is the section named by `AlgebraicGeometry.Stack.genericProductPoint`, and its
bottom edge is the unique morphism to the representable terminal presheaf. -/
noncomputable def presheafSquareOfStack {f : 𝒳 ⟶ 𝒴} (q : ValuativeSquare B S hS f)
    (F : (siteOver B (siteObject B S hS q.ring_mem q.base))ᵒᵖ ⥤ Type u)
    (e : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map (siteObject B S hS q.ring_mem q.base).hom)
        𝒳.val.val.p 𝒴.val.val.p
        (sitePointOfSchemePoint B (siteObject B S hS q.ring_mem q.base) q.y)
        f.hom.hom.toFunctor)
      (presheafOfCategories (F ⋙ typeToCat)).p) :
    Space.ValuativeSquare
      ((Space.isTerminal_yoneda_obj_base B (siteObject B S hS q.ring_mem q.base).left.1
        (siteObject B S hS q.ring_mem q.base).left.2).from F) := by
  have hP : (TwoFibreProductOver.fst (Over.map (siteObject B S hS q.ring_mem q.base).hom)
      𝒳.val.val.p 𝒴.val.val.p
      (sitePointOfSchemePoint B (siteObject B S hS q.ring_mem q.base) q.y)
      f.hom.hom.toFunctor).obj (genericProductPoint B q) =
      siteObject B (siteObject B S hS q.ring_mem q.base).left.1
        (siteObject B S hS q.ring_mem q.base).left.2 q.field_mem
        (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ 𝟙 _) := by
    rw [Category.comp_id]
    rfl
  exact
    { R := q.R, K := q.K, ring_mem := q.ring_mem, field_mem := q.field_mem
      base := 𝟙 _
      generic := yonedaEquiv.symm (sectionOfObj e (genericProductPoint B q) hP)
      special := (Space.isTerminal_yoneda_obj_base B
        (siteObject B S hS q.ring_mem q.base).left.1
        (siteObject B S hS q.ring_mem q.base).left.2).from _
      comm := (Space.isTerminal_yoneda_obj_base B
        (siteObject B S hS q.ring_mem q.base).left.1
        (siteObject B S hS q.ring_mem q.base).left.2).hom_ext _ _ }

end Auxiliary

/-- **A dominating extension by bijective ring maps does not enlarge the set of dotted arrows.**
If the two homomorphisms of a dominating extension of a valuative square for a morphism of
presheaves are bijective, a dotted arrow for the extended square restricts to one for the original
square.

The inverse homomorphisms induce morphisms of site objects in the other direction, and the three
equalities they satisfy — two retractions and one commuting square — are equalities of morphisms
of spectra, so no transport along an equality of site objects is needed. -/
private theorem nonempty_lift_of_bijective {B : BigFppfSite.{u}} {T : Scheme.{u}}
    {hT : B.Contains T} {X Y : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u} {g : X ⟶ Y}
    {q : Space.ValuativeSquare g} (d : q.DominatingExtension)
    (hring : Function.Bijective d.ringMap) (hfield : Function.Bijective d.fieldMap)
    (l : d.square.Lift) : Nonempty q.Lift := by
  let ri : d.square.R →+* q.R := (RingEquiv.ofBijective d.ringMap hring).symm.toRingHom
  let fi : d.square.K →+* q.K := (RingEquiv.ofBijective d.fieldMap hfield).symm.toRingHom
  have hri : ri.comp d.ringMap = RingHom.id q.R :=
    RingHom.ext fun x => (RingEquiv.ofBijective d.ringMap hring).symm_apply_apply x
  have hfi : fi.comp d.fieldMap = RingHom.id q.K :=
    RingHom.ext fun x => (RingEquiv.ofBijective d.fieldMap hfield).symm_apply_apply x
  have hfrac : (algebraMap q.R q.K).comp ri = fi.comp (algebraMap d.square.R d.square.K) := by
    refine RingHom.ext fun x => ?_
    obtain ⟨x₀, rfl⟩ := hring.surjective x
    have h1 : ri (d.ringMap x₀) = x₀ := RingHom.congr_fun hri x₀
    have h2 : algebraMap d.square.R d.square.K (d.ringMap x₀) =
      d.fieldMap (algebraMap q.R q.K x₀) := RingHom.congr_fun d.fraction_comm x₀
    have h3 : fi (d.fieldMap (algebraMap q.R q.K x₀)) = algebraMap q.R q.K x₀ :=
      RingHom.congr_fun hfi (algebraMap q.R q.K x₀)
    simp only [RingHom.comp_apply, h1, h2, h3]
  have hid : Spec.map (CommRingCat.ofHom ri) ≫ Spec.map (CommRingCat.ofHom d.ringMap) =
      𝟙 (Spec (.of q.R)) := by
    rw [← ValuativeSquare.specMap_ofHom_comp, hri, CommRingCat.ofHom_id, Spec.map_id]
  have hidK : Spec.map (CommRingCat.ofHom fi) ≫ Spec.map (CommRingCat.ofHom d.fieldMap) =
      𝟙 (Spec (.of q.K)) := by
    rw [← ValuativeSquare.specMap_ofHom_comp, hfi, CommRingCat.ofHom_id, Spec.map_id]
  have hbase : Spec.map (CommRingCat.ofHom ri) ≫ d.square.base = q.base := by
    rw [d.base_comm, ← Category.assoc, hid, Category.id_comp]
  let a₀ : siteObject B T hT q.ring_mem q.base ⟶
      siteObject B T hT d.square.ring_mem d.square.base :=
    Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom ri)) :
      B.obj q.ring_mem ⟶ B.obj d.square.ring_mem) (ObjectProperty.hom_ext _ hbase)
  let k₀ : siteObject B T hT q.field_mem
        (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base) ⟶
      siteObject B T hT d.square.field_mem
        (Spec.map (CommRingCat.ofHom (algebraMap d.square.R d.square.K)) ≫ d.square.base) :=
    Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom fi)) :
      B.obj q.field_mem ⟶ B.obj d.square.field_mem) (by
      apply ObjectProperty.hom_ext
      show Spec.map (CommRingCat.ofHom fi) ≫
        (Spec.map (CommRingCat.ofHom (algebraMap d.square.R d.square.K)) ≫ d.square.base) =
        Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base
      rw [← Category.assoc, ← ValuativeSquare.specMap_ofHom_comp, ← hfrac,
        ValuativeSquare.specMap_ofHom_comp, Category.assoc, hbase])
  have h1 : a₀ ≫ d.specialOver = 𝟙 (siteObject B T hT q.ring_mem q.base) := by
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    show Spec.map (CommRingCat.ofHom ri) ≫ B.inclusion.map d.specialOver.left = 𝟙 _
    rwa [d.specialOver_left]
  have h2 : k₀ ≫ d.genericOver = 𝟙 (siteObject B T hT q.field_mem
      (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)) := by
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    show Spec.map (CommRingCat.ofHom fi) ≫ B.inclusion.map d.genericOver.left = 𝟙 _
    rwa [d.genericOver_left]
  have h3 : q.genericMap ≫ a₀ = k₀ ≫ d.square.genericMap := by
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    show Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ Spec.map (CommRingCat.ofHom ri) =
      Spec.map (CommRingCat.ofHom fi) ≫
        Spec.map (CommRingCat.ofHom (algebraMap d.square.R d.square.K))
    rw [← ValuativeSquare.specMap_ofHom_comp, ← ValuativeSquare.specMap_ofHom_comp, hfrac]
  refine ⟨{ map := yoneda.map a₀ ≫ l.map, generic_comm := ?_, special_comm := ?_ }⟩
  · calc yoneda.map q.genericMap ≫ yoneda.map a₀ ≫ l.map
        = yoneda.map (q.genericMap ≫ a₀) ≫ l.map := by
          rw [Functor.map_comp, Category.assoc]
      _ = yoneda.map k₀ ≫ yoneda.map d.square.genericMap ≫ l.map := by
          rw [h3, Functor.map_comp, Category.assoc]
      _ = yoneda.map (k₀ ≫ d.genericOver) ≫ q.generic := by
          rw [l.generic_comm, d.generic_comm, Functor.map_comp, Category.assoc]
      _ = q.generic := by rw [h2, CategoryTheory.Functor.map_id, Category.id_comp]
  · calc (yoneda.map a₀ ≫ l.map) ≫ g
        = yoneda.map (a₀ ≫ d.specialOver) ≫ q.special := by
          rw [Category.assoc, l.special_comm, d.special_comm, Functor.map_comp, Category.assoc]
      _ = q.special := by rw [h1, CategoryTheory.Functor.map_id, Category.id_comp]

/-- **The link of a point of the base change whose site component is a spectrum.** If the site
component of an object `AR` of the base change of `q` is the site object attached to a ring
homomorphism out of the valuation ring of `q`, then the link of `AR` lies over the morphism of site
objects that homomorphism induces.

Destructuring `AR` and substituting the hypothesis makes the morphism of
`AlgebraicGeometry.Stack.productPointLink_lift` literally the one in the statement, so no transport
along an equality of objects is needed. -/
private theorem isHomLift_productPointLink_homMk
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ 𝒴} (q : ValuativeSquare B S hS f)
    {R₂ : Type u} [CommRing R₂] (hR₂ : B.Contains (Spec (.of R₂))) (a : q.R →+* R₂)
    (AR : valuativeBaseChange B q)
    (hAR : AR.x = siteObject B (siteObject B S hS q.ring_mem q.base).left.1
      (siteObject B S hS q.ring_mem q.base).left.2 hR₂ (Spec.map (CommRingCat.ofHom a))) :
    𝒴.val.val.p.IsHomLift
      (Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom a))) :
        siteObject B S hS hR₂ (Spec.map (CommRingCat.ofHom a) ≫ q.base) ⟶
          siteObject B S hS q.ring_mem q.base)
      (productPointLink B q AR) := by
  have h := productPointLink_lift B q AR
  obtain ⟨Abase, Ax, Ay, Ahx, Ahy, Aiso, Avert⟩ := AR
  subst hAR
  subst Ahx
  exact h

/-- **Lifting is insensitive to the endpoints and to the representative of a site morphism.** A
morphism lying over `r` also lies over `r'` when the endpoints are equal and the underlying
morphisms of schemes agree. -/
private theorem isHomLift_of_inclusion_map_left_heq {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {𝒳 : Type*} [Category 𝒳] {p : 𝒳 ⥤ BigFppfOver B S hS}
    {X Y X' Y' : BigFppfOver B S hS} {za zb : 𝒳} {r : X ⟶ Y} {φ : za ⟶ zb}
    (hφ : p.IsHomLift r φ) (r' : X' ⟶ Y') (hX : X = X') (hY : Y = Y')
    (h : HEq (B.inclusion.map r.left) (B.inclusion.map r'.left)) : p.IsHomLift r' φ := by
  subst hX hY
  rwa [Over.OverMorphism.ext (B.inclusion.map_injective (eq_of_heq h)) (g := r')] at hφ

/-- **The common core of the forward direction of Stacks 0CLN at a point.** A valuative square `q`
for the representing presheaf is turned into a valuative square `Q` for `f` over the base: its
generic point is named by an object of the 2-fibre product, that object and the value of the point
at the spectrum of the valuation ring are the values at the unit objects of 1-morphisms out of
slices, and the filling 2-morphism is the 2-Yoneda extension of the comparison morphism between
them. A dotted arrow for a dominating extension of `Q` is a span in `𝒳` compatible with the link of
`Q`, which by `CategoryTheory.TwoFibreProductOver.exists_section_of_span` produces the section of
the presheaf that is the dotted arrow sought.

The valuation ring and the fraction field of `Q` are those of `q`, so the predicate `Pred` on
valuation rings transfers to the hypothesis for free, and the dominating extension of `q` that
comes out is the one along the very homomorphisms of the dominating extension of `Q` that the
hypothesis produced; the predicate `ExtPred` on those homomorphisms therefore transfers back.
Taking both predicates to be trivially true gives the existence criterion for `p`, and taking
`ExtPred` to be bijectivity of the two homomorphisms gives a dotted arrow for `q` itself.

No representability hypothesis is needed: the equivalence `e` is given. -/
private theorem exists_dominatingExtension_lift_core
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (Pred : ∀ R : Type u, [CommRing R] → [IsDomain R] → [ValuationRing R] → Prop)
    (ExtPred : ∀ R R' K K' : Type u, (R → R') → (K → K') → Prop)
    (H : ∀ Q : ValuativeSquare B S hS f, Pred Q.R →
      ∃ d : Q.DominatingExtension,
        ExtPred Q.R d.R' Q.K d.K' d.ringMap d.fieldMap ∧
        Nonempty (DottedArrow (d.k ≫ Q.x) d.j f.hom (d.a ≫ Q.y) d.inducedGamma))
    (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.val.obj)
    (hy : y ⋙ 𝒴.val.val.p = Over.map U.hom)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (e : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.val.p 𝒴.val.val.p y
        f.hom.hom.toFunctor)
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (p : F ⟶ yoneda.obj (Over.mk (𝟙 (B.obj U.left.2))))
    (q : Space.ValuativeSquare p) (hq : Pred q.R) :
    ∃ e₁ : q.DominatingExtension,
      ExtPred q.R e₁.square.R q.K e₁.square.K e₁.ringMap e₁.fieldMap ∧
      Nonempty e₁.square.Lift := by
  classical
  let pU : BigFppfOver B U.left.1 U.left.2 ⥤ BigFppfOver B S hS := Over.map U.hom
  let RU := siteObject B U.left.1 U.left.2 q.ring_mem q.base
  let KU := siteObject B U.left.1 U.left.2 q.field_mem
    (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)
  let ju : KU ⟶ RU := q.genericMap
  let RS := siteObject B S hS q.ring_mem (q.base ≫ U.hom.hom)
  let KS := siteObject B S hS q.field_mem
    (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base ≫ U.hom.hom)
  let js : KS ⟶ RS := Over.homMk
    (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K))))
  have hKS : pU.obj KU = KS := by
    show Over.mk _ = Over.mk _
    congr 1
  obtain ⟨X, hX, i, hi, hz⟩ :=
    TwoFibreProductOver.exists_mk_of_section e KU (yonedaEquiv q.generic)
  let A : TwoFibreProductOver pU 𝒳.val.val.p 𝒴.val.val.p y f.hom.hom.toFunctor :=
    ⟨pU.obj KU, KU, X, rfl, hX, i, hi⟩
  have hY : 𝒴.val.val.p.obj (y.obj RU) = RS := Functor.congr_obj hy RU
  obtain ⟨G, cG, hcG⟩ := Functor.TwoYoneda.exists_basedFunctor_unitHom 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids X (hX.trans hKS)
  obtain ⟨L, cL, hcL⟩ := Functor.TwoYoneda.exists_basedFunctor_unitHom 𝒴.val.val.p
    𝒴.val.isFiberedInGroupoids (y.obj RU) hY
  have hcGiso : IsIso cG :=
    Functor.isIso_of_fiber_isGroupoid
      (𝒳.val.isFiberedInGroupoids.fiber_isGroupoid KS) cG hcG
  have : IsIso cL :=
    Functor.isIso_of_fiber_isGroupoid
      (𝒴.val.isFiberedInGroupoids.fiber_isGroupoid RS) cL hcL
  have hiinv : 𝒴.val.val.p.IsHomLift (𝟙 (pU.obj KU)) i.inv := by
    have h : 𝒴.val.val.p.IsHomLift (𝟙 (pU.obj KU)) (inv i.hom) :=
      have := hi
      IsHomLift.lift_id_inv_isIso 𝒴.val.val.p (pU.obj KU) i.hom
    rwa [IsIso.Iso.inv_hom] at h
  have hju : 𝒴.val.val.p.IsHomLift (pU.map ju) (y.map ju) :=
    have := IsHomLift.map pU ju
    Functor.isHomLift_map_of_comp_eq hy (pU.map ju) ju
  have hc : 𝒴.val.val.p.IsHomLift (pU.map ju) (i.inv ≫ y.map ju) :=
    @IsHomLift.comp_lift_id_left _ _ _ _ 𝒴.val.val.p _ _ _ _ _
      (pU.map ju) (y.map ju) hju i.inv hiinv
  have hc' : 𝒴.val.val.p.IsHomLift js (i.inv ≫ y.map ju) := by
    refine Functor.isHomLift_of_base_eq (pU.map ju) _ hc js hKS rfl ?_
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    simp
    rfl
  have hfcG : 𝒴.val.val.p.IsHomLift (𝟙 KS) (f.hom.hom.map cG) :=
    have : (BasedCategory.ofFunctor 𝒳.val.val.p).p.IsHomLift (𝟙 KS) cG := hcG
    f.hom.hom.preserves_isHomLift _ _
  have hcLinv : 𝒴.val.val.p.IsHomLift (𝟙 RS) (inv cL) :=
    IsHomLift.lift_id_inv_isIso 𝒴.val.val.p RS cL
  let c := f.hom.hom.map cG ≫ (i.inv ≫ y.map ju) ≫ inv cL
  have hc₀ : 𝒴.val.val.p.IsHomLift js (f.hom.hom.map cG ≫ (i.inv ≫ y.map ju)) :=
    @IsHomLift.comp_lift_id_left _ _ _ _ 𝒴.val.val.p _ _ _ _ _
      js (i.inv ≫ y.map ju) hc' (f.hom.hom.map cG) hfcG
  have hc₁ : 𝒴.val.val.p.IsHomLift js c := by
    have hc₂ := @IsHomLift.comp_lift_id_right _ _ _ _ 𝒴.val.val.p _ _ _ _ _
      js (f.hom.hom.map cG ≫ (i.inv ≫ y.map ju)) hc₀ (inv cL) hcLinv
    simpa only [c, Category.assoc] using hc₂
  let δ := Functor.TwoYoneda.homOverBase 𝒴.val.val.p js 𝒴.val.isFiberedInGroupoids
    (G := BasedFunctor.comp G f.hom.hom) (H := L) c hc₁
  have hδiso : IsIso δ :=
    Functor.TwoYoneda.isIso_hom 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids δ
  let γQ := @inv _ _ _ _ δ hδiso
  let Q : ValuativeSquare B S hS f :=
    { R := q.R, K := q.K, ring_mem := q.ring_mem, field_mem := q.field_mem
      base := q.base ≫ U.hom.hom
      genericMap := js
      genericMap_left := rfl
      j := schemeMorphism B js
      j_canonical := rfl
      x := Bicategory.InducedBicategory.mkHom G
      y := Bicategory.InducedBicategory.mkHom L
      γ := ⟨γQ⟩ }
  have hcQ : pointLink B Q = c := by
    have hδfac := Functor.TwoYoneda.homOverBase_fac 𝒴.val.val.p js
      𝒴.val.isFiberedInGroupoids (G := BasedFunctor.comp G f.hom.hom) (H := L) c hc₁
    have : IsIso (γQ.app (Over.mk (𝟙 KS))) :=
      Functor.isIso_of_fiber_isGroupoid
        (𝒴.val.isFiberedInGroupoids.fiber_isGroupoid KS) _
        (γQ.isHomLift' (Over.mk (𝟙 KS)))
    have hcomp : γQ.app (Over.mk (𝟙 KS)) ≫ δ.app (Over.mk (𝟙 KS)) = 𝟙 _ :=
      congrArg (fun η => η.app (Over.mk (𝟙 KS))) (@IsIso.inv_hom_id _ _ _ _ δ hδiso)
    show inv (γQ.app (Over.mk (𝟙 KS))) ≫ _ = c
    rw [IsIso.inv_eq_of_hom_inv_id hcomp]
    exact hδfac
  obtain ⟨d, hdExt, ⟨l⟩⟩ := H Q hq
  obtain ⟨ZK, ZR, n, m, b, hn, hm, hb, hspan⟩ := exists_span_of_dottedArrow B Q d l
  have hn' : 𝒳.val.val.p.IsHomLift d.genericOver (n ≫ cG) :=
    @IsHomLift.comp_lift_id_right _ _ _ _ 𝒳.val.val.p _ _ _ _ _
      d.genericOver n hn cG hcG
  have hb' : 𝒴.val.val.p.IsHomLift d.specialOver (b ≫ cL) :=
    @IsHomLift.comp_lift_id_right _ _ _ _ 𝒴.val.val.p _ _ _ _ _
      d.specialOver b hb cL hcL
  have hspan' : f.hom.hom.map (n ≫ cG) ≫ A.iso.inv ≫ y.map ju =
      f.hom.hom.map m ≫ (b ≫ cL) := by
    have hh := congrArg (fun t => t ≫ cL) hspan
    rw [hcQ] at hh
    simpa only [c, A, f.hom.hom.toFunctor.map_comp, Category.assoc,
      IsIso.inv_hom_id, Category.comp_id] using hh
  let R₁ := siteObject B U.left.1 U.left.2 d.ring_mem
    (Spec.map (CommRingCat.ofHom d.ringMap) ≫ q.base)
  let K₁ := siteObject B U.left.1 U.left.2 d.field_mem
    (Spec.map (CommRingCat.ofHom (algebraMap d.R' d.K')) ≫
      Spec.map (CommRingCat.ofHom d.ringMap) ≫ q.base)
  have hfrac : Spec.map (CommRingCat.ofHom (algebraMap d.R' d.K')) ≫
      Spec.map (CommRingCat.ofHom d.ringMap) =
      Spec.map (CommRingCat.ofHom d.fieldMap) ≫
        Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) := by
    rw [← ValuativeSquare.specMap_ofHom_comp, ← ValuativeSquare.specMap_ofHom_comp,
      d.fraction_comm]
  let a' : R₁ ⟶ RU := Over.homMk
    (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom d.ringMap)))
  let j' : K₁ ⟶ R₁ := Over.homMk
    (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap d.R' d.K'))))
  let k' : K₁ ⟶ KU := Over.homMk
    (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom d.fieldMap))) (by
      apply ObjectProperty.hom_ext
      show Spec.map (CommRingCat.ofHom d.fieldMap) ≫
        (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base) = _
      rw [← Category.assoc, ← hfrac, Category.assoc]
      rfl)
  have hsq : j' ≫ a' = k' ≫ ju := Over.OverMorphism.ext (B.inclusion.map_injective hfrac)
  have hR₁ : pU.obj R₁ = siteObject B S hS d.ring_mem
      (Spec.map (CommRingCat.ofHom d.ringMap) ≫ Q.base) := by
    show Over.mk _ = Over.mk _
    congr 1
  have hK₁ : pU.obj K₁ = siteObject B S hS d.field_mem
      (Spec.map (CommRingCat.ofHom (algebraMap d.R' d.K')) ≫
        Spec.map (CommRingCat.ofHom d.ringMap) ≫ Q.base) := by
    show Over.mk _ = Over.mk _
    congr 1
  have hn'' : 𝒳.val.val.p.IsHomLift (pU.map k') (n ≫ cG) := by
    exact isHomLift_of_inclusion_map_left_heq hn' _ hK₁.symm hKS.symm
      (heq_of_eq d.genericOver_left)
  have hm' : 𝒳.val.val.p.IsHomLift (pU.map j') m :=
    isHomLift_of_inclusion_map_left_heq hm _ hK₁.symm hR₁.symm (heq_of_eq d.genericMap_left)
  have hb'' : 𝒴.val.val.p.IsHomLift (pU.map a') (b ≫ cL) :=
    isHomLift_of_inclusion_map_left_heq hb' _ hR₁.symm rfl (heq_of_eq d.specialOver_left)
  obtain ⟨z, hgen⟩ := TwoFibreProductOver.exists_section_of_span e
    𝒴.val.isFiberedInGroupoids hy f.hom.hom.w A ju a' k' j' hsq
    (n ≫ cG) m (b ≫ cL) hn'' hm' hb'' hspan'
  rw [show sectionOfObj e A rfl = yonedaEquiv q.generic from hz] at hgen
  let q₁ : Space.ValuativeSquare p :=
    { R := d.R', K := d.K', ring_mem := d.ring_mem, field_mem := d.field_mem
      base := Spec.map (CommRingCat.ofHom d.ringMap) ≫ q.base
      generic := yoneda.map k' ≫ q.generic
      special := yoneda.map a' ≫ q.special
      comm := (Space.isTerminal_yoneda_obj_base B U.left.1 U.left.2).hom_ext _ _ }
  let e₁ : q.DominatingExtension :=
    { square := q₁, ringMap := d.ringMap, fieldMap := d.fieldMap
      isLocalHom := d.isLocalHom, fraction_comm := d.fraction_comm
      base_comm := rfl
      genericOver := k', genericOver_left := rfl
      specialOver := a', specialOver_left := rfl
      generic_comm := rfl, special_comm := rfl }
  refine ⟨e₁, hdExt, ⟨Space.ValuativeSquare.liftOfSection q₁ z ?_ ?_⟩⟩
  · show F.map j'.op z = yonedaEquiv (yoneda.map k' ≫ q.generic)
    rwa [← yonedaEquiv.symm_apply_apply q.generic, yonedaEquiv_symm_naturality_left,
      Equiv.apply_symm_apply]
  · exact Over.mkIdTerminal.hom_ext _ _

/-- **Stacks 0CLN, the forward direction.** If `f` satisfies the existence part of the valuative
criterion, then so does the structure morphism of every algebraic space representing a base change
of `f` along a scheme-valued point of the target.

A valuative square `q` for the representing presheaf is turned into a valuative square `Q` for `f`
over the base: its generic point is named by an object of the 2-fibre product, that object and the
value of the point at the spectrum of the valuation ring are the values at the unit objects of
1-morphisms out of slices, and the filling 2-morphism is the 2-Yoneda extension of the comparison
morphism between them. A dotted arrow for `Q` is a span in `𝒳` compatible with the link of `Q`,
which by `CategoryTheory.TwoFibreProductOver.exists_section_of_span` produces the section of the
presheaf that is the dotted arrow sought.

No representability hypothesis is needed: the equivalence `e` is given. -/
theorem valuativeCriterionExistence_baseChange_point
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (H : ValuativeCriterion.Existence B S hS f) (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.val.obj)
    (hy : y ⋙ 𝒴.val.val.p = Over.map U.hom)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (e : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.val.p 𝒴.val.val.p y
        f.hom.hom.toFunctor)
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (p : F ⟶ yoneda.obj (Over.mk (𝟙 (B.obj U.left.2)))) :
    Space.ValuativeCriterion.Existence p := by
  intro q
  obtain ⟨e₁, -, hl⟩ := exists_dominatingExtension_lift_core B S hS f
    (fun _ _ _ _ => True) (fun _ _ _ _ _ _ => True)
    (fun Q _ => (H Q).imp fun d hd => ⟨trivial, hd⟩) U y hy F e p q trivial
  exact ⟨e₁, hl⟩

/-- **A dotted arrow over the valuation ring itself, transported to the algebraic-space base
changes.** This strengthens `AlgebraicGeometry.Stack.valuativeCriterionExistence_baseChange_point`:
if every valuative square for `f` whose valuation ring satisfies `Pred` already admits a dotted
arrow — with no extension of the fraction field and no passage to a dominating valuation ring —
then so does every valuative square for the structure morphism of an algebraic space representing
a base change of `f` along a scheme-valued point of the target, over the *same* valuation ring.

The predicate `Pred` is carried along because the valuation ring of the valuative square for `f`
built from `q` is literally that of `q`; taking `Pred` to be `IsDiscreteValuationRing` restricts
the hypothesis to discretely valued squares, and taking it to be constantly true drops it.

The square for `f` is filled by the hypothesis, read as a dotted arrow for the identity dominating
extension through `AlgebraicGeometry.Stack.dominatingExtensionOfRingMaps`; the dominating extension
of `q` that comes back is therefore the one along the identity homomorphisms, and a dotted arrow
for it is one for `q`. -/
theorem nonempty_lift_baseChange_point
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (Pred : ∀ R : Type u, [CommRing R] → [IsDomain R] → [ValuationRing R] → Prop)
    (H : ∀ Q : ValuativeSquare B S hS f, Pred Q.R →
      Nonempty (DottedArrow Q.x Q.j f.hom Q.y Q.γ))
    (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.val.obj)
    (hy : y ⋙ 𝒴.val.val.p = Over.map U.hom)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (e : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.val.p 𝒴.val.val.p y
        f.hom.hom.toFunctor)
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (p : F ⟶ yoneda.obj (Over.mk (𝟙 (B.obj U.left.2))))
    (q : Space.ValuativeSquare p) (hq : Pred q.R) :
    Nonempty q.Lift := by
  have key : ∀ Q : ValuativeSquare B S hS f, Pred Q.R →
      ∃ d : Q.DominatingExtension,
        (Function.Bijective d.ringMap ∧ Function.Bijective d.fieldMap) ∧
        Nonempty (DottedArrow (d.k ≫ Q.x) d.j f.hom (d.a ≫ Q.y) d.inducedGamma) := by
    intro Q hQ
    obtain ⟨l₀⟩ := H Q hQ
    exact ⟨dominatingExtensionOfRingMaps B Q Q.R Q.K (RingHom.id Q.R) (RingHom.id Q.K)
      (isLocalHom_id Q.R) (by rw [RingHom.comp_id, RingHom.id_comp]) Q.ring_mem Q.field_mem,
      ⟨Function.bijective_id, Function.bijective_id⟩, ⟨extendDottedArrow B Q _ l₀⟩⟩
  obtain ⟨e₁, ⟨hr, hk⟩, ⟨l⟩⟩ := exists_dominatingExtension_lift_core B S hS f Pred
    (fun _ _ _ _ a k => Function.Bijective a ∧ Function.Bijective k) key U y hy F e p q hq
  exact nonempty_lift_of_bijective e₁ hr hk l

/-- **Stacks 0CLN, the backward direction.** If the structure morphism of every algebraic space
representing a base change of `f` along a scheme-valued point of the target satisfies the
existence part of the valuative criterion, then so does `f`.

A valuative square `q` for `f` is base-changed along its own special point; the generic point of
`q` names a section of the representing presheaf, and together with the terminal structure
morphism this is a valuative square for that presheaf. A dotted arrow for it names a second
section, and the two sections are related by two morphisms of the 2-fibre product whose
`𝒳`-components form a span compatible with the link of `q`; that span is a dotted arrow for the
outer rectangle of the dominating extension the hypothesis produced. -/
theorem valuativeCriterionExistence_of_baseChange
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    (H : ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.val.obj)
      (_hy : y ⋙ 𝒴.val.val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (_hF : IsAlgebraicSpace B U.left.1 U.left.2 F)
      (_e : StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.val.p 𝒴.val.val.p y
          f.hom.hom.toFunctor)
        (presheafOfCategories (F ⋙ typeToCat)).p)
      (p : F ⟶ yoneda.obj (Over.mk (𝟙 (B.obj U.left.2)))),
      Space.ValuativeCriterion.Existence p) :
    ValuativeCriterion.Existence B S hS f := by
  classical
  intro q
  let U := siteObject B S hS q.ring_mem q.base
  let y := sitePointOfSchemePoint B U q.y
  have hy : y ⋙ 𝒴.val.val.p = Over.map U.hom :=
    sitePointOfSchemePoint_compatible B U q.y
  obtain ⟨F, hF, ⟨e⟩⟩ := hf U y hy
  let p := (Space.isTerminal_yoneda_obj_base B U.left.1 U.left.2).from F
  let Q := presheafSquareOfStack B q F e
  obtain ⟨d, ⟨l⟩⟩ := H U y hy F hF e p Q
  let pP := TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.val.p 𝒴.val.val.p y
    f.hom.hom.toFunctor
  let KR := siteObject B U.left.1 U.left.2 d.square.field_mem
    (Spec.map (CommRingCat.ofHom (algebraMap d.square.R d.square.K)) ≫ d.square.base)
  let RR := siteObject B U.left.1 U.left.2 d.square.ring_mem d.square.base
  let jr : KR ⟶ RR := d.square.genericMap
  obtain ⟨AK, hAK, hK⟩ := exists_sectionOfObj e (yonedaEquiv d.square.generic)
  obtain ⟨AR, hAR, hR⟩ := exists_sectionOfObj e (yonedaEquiv l.map)
  have hj : F.map jr.op (sectionOfObj e AR hAR) = sectionOfObj e AK hAK := by
    rw [hK, hR]
    simpa only [yonedaEquiv_naturality] using congrArg yonedaEquiv l.generic_comm
  obtain ⟨m, hm⟩ := exists_hom_of_sectionOfObj_map e hAR hAK jr hj.symm
  have hA : pP.obj (genericProductPoint B q) =
      siteObject B U.left.1 U.left.2 q.field_mem
      (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ 𝟙 _) := by
    rw [Category.comp_id]
    rfl
  have hk : sectionOfObj e AK hAK =
      F.map d.genericOver.op (sectionOfObj e (genericProductPoint B q) hA) := by
    refine hK.trans ((congrArg yonedaEquiv d.generic_comm).trans ?_)
    refine Eq.trans (congrArg yonedaEquiv (yonedaEquiv_symm_naturality_left
      d.genericOver F (sectionOfObj e (genericProductPoint B q) hA))) ?_
    exact yonedaEquiv.apply_symm_apply _
  obtain ⟨n, hn⟩ := exists_hom_of_sectionOfObj_map e hA hAK d.genericOver hk
  let e₁ := dominatingExtensionOfRingMaps B q d.square.R d.square.K
    d.ringMap d.fieldMap d.isLocalHom d.fraction_comm d.square.ring_mem d.square.field_mem
  have hbase : d.square.base = Spec.map (CommRingCat.ofHom d.ringMap) :=
    d.base_comm.trans (Category.comp_id _)
  have hRR : (Over.map U.hom).obj RR = siteObject B S hS e₁.ring_mem
      (Spec.map (CommRingCat.ofHom e₁.ringMap) ≫ q.base) := by
    refine congrArg Over.mk (ObjectProperty.hom_ext _ ?_)
    show d.square.base ≫ q.base = Spec.map (CommRingCat.ofHom d.ringMap) ≫ q.base
    rw [hbase]
    rfl
  have hKR : (Over.map U.hom).obj KR = siteObject B S hS e₁.field_mem
      (Spec.map (CommRingCat.ofHom (algebraMap e₁.R' e₁.K')) ≫
        Spec.map (CommRingCat.ofHom e₁.ringMap) ≫ q.base) := by
    refine congrArg Over.mk (ObjectProperty.hom_ext _ ?_)
    show (Spec.map (CommRingCat.ofHom (algebraMap d.square.R d.square.K)) ≫
      d.square.base) ≫ q.base = _
    rw [hbase]
    exact Category.assoc _ _ _
  have hK₀ : (Over.map U.hom).obj (siteObject B U.left.1 U.left.2 q.field_mem
      (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ 𝟙 _)) =
      siteObject B S hS q.field_mem
        (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base) := by
    refine congrArg Over.mk (ObjectProperty.hom_ext _ ?_)
    show (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ 𝟙 _) ≫ q.base = _
    rw [Category.comp_id]
    rfl
  refine ⟨e₁, nonempty_dottedArrow_of_span B q e₁ n.b ?_ m.b ?_
    (productPointLink B q AR) ?_ ?_⟩
  · exact isHomLift_of_inclusion_map_left_heq
      (TwoFibreProductOver.isHomLift_b_of_isHomLift_fst d.genericOver n hn) _ hKR hK₀
      (heq_of_eq (d.genericOver_left.trans e₁.genericOver_left.symm))
  · exact isHomLift_of_inclusion_map_left_heq
      (TwoFibreProductOver.isHomLift_b_of_isHomLift_fst jr m hm) _ hKR hRR HEq.rfl
  · exact isHomLift_productPointLink_homMk B S hS q d.square.ring_mem d.ringMap AR
      (hAR.trans (by rw [hbase]; rfl))
  · refine Eq.trans (congrArg (fun t => f.hom.hom.map n.b ≫ t)
      (genericProductPoint_link B q).symm) ?_
    exact (productPointLink_map B q n).trans (productPointLink_map B q m).symm

/-- **Stacks 0CLN.** For a 1-morphism of algebraic stacks representable by algebraic spaces, the
existence part of the valuative criterion holds exactly when it holds for every base change to an
algebraic space along a scheme-valued point of the target.

The base change is described exactly as in Stacks 02ZW: for an object `U` of the site and a
scheme-valued point `y` of `𝒴` over `U`, it is the first projection of the 2-fibre product
`U ×_𝒴 𝒳`, and the condition is imposed on the structure morphism of *any* algebraic space `F`
over `U` equivalent to it over the site of `U`. Quantifying over all such `F` rather than over a
chosen one spares a consumer the transport along a comparison equivalence. -/
@[stacks 0CLN]
theorem valuativeCriterionExistence_iff_baseChange (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom) :
    ValuativeCriterion.Existence B S hS f ↔
      ∀ U : BigFppfOver B S hS,
        let 𝒰 := BigFppfOver B U.left.1 U.left.2
        let p𝒰 : 𝒰 ⥤ BigFppfOver B S hS := Over.map U.hom
        ∀ (y : 𝒰 ⥤ 𝒴.val.val.obj) (_hy : y ⋙ 𝒴.val.val.p = p𝒰) (F : 𝒰ᵒᵖ ⥤ Type u)
          (_hF : IsAlgebraicSpace B U.left.1 U.left.2 F)
          (_e : StacksRepresentableCFG.EquivalenceOver
            (TwoFibreProductOver.fst p𝒰 𝒳.val.val.p 𝒴.val.val.p y f.hom.hom.toFunctor)
            (presheafOfCategories (F ⋙ typeToCat)).p)
          (p : F ⟶ yoneda.obj (Over.mk (𝟙 (B.obj U.left.2)))),
          Space.ValuativeCriterion.Existence p :=
  ⟨fun H U y hy F _ e p => valuativeCriterionExistence_baseChange_point B S hS f H U y hy F e p,
    fun H => valuativeCriterionExistence_of_baseChange B S hS f hf
      fun U y hy F hF e p => H U y hy F hF e p⟩

end AlgebraicGeometry.Stack

end
