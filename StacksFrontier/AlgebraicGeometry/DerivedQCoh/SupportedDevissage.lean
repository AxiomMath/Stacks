module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.TildeFactorization
public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.DerivedRestrictUnit
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.WeakSerre.DerivedComparison
public import StacksFrontier.AlgebraicGeometry.AffineVanishingQuasicoherentComplex
public import StacksFrontier.Homology.PseudoCoherent.Locality
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.PushforwardAndRestriction

/-!
# Dévissage of a complex with closed support along a finite affine cover

Let `X` be a quasi-compact scheme and let `E` be an object of `D(𝒪_X)` whose cohomology sheaves
are supported on a closed subset `S`. Covering `X` by finitely many affine opens
`U₁, …, Uₙ` and removing one `Uᵢ` at a time shrinks the support, after `n` steps to the empty
set — where the object is zero. This file packages that induction as
`Stacks.DerivedQCoh.property_of_finite_affine_support`: a property `P` of objects of `D(𝒪_X)`
which holds at zero, is stable under the two outer vertices of a distinguished triangle, and
which the dévissage step produces at the middle vertex, holds at every object satisfying the
auxiliary property `Q` the step is allowed to assume.

The step itself is the content of [Stacks, Tag 09T6]; it is not here. What is here is the
induction and the support bookkeeping it needs: that the cone of a map which becomes invertible
after restriction to `U` is supported on `S \ U`
(`Stacks.DerivedQCoh.exists_cocone_supportedOn_inter_compl`), that restriction to an open
pulls the supporting set back and preserves quasi-coherence of the cohomology sheaves, and that
an object supported on `∅` vanishes.

## Main definitions

None; every statement below is about
`Stacks.Cohomology.PushforwardRestriction.CohomologySupportedOn`.

## Main results

* `Stacks.DerivedQCoh.property_of_finite_affine_support` — the finite affine-cover induction.
* `Stacks.DerivedQCoh.exists_cocone_supportedOn_inter_compl` — the cone of a morphism between
  objects supported on a closed `T` which becomes invertible after restriction to an open `U`
  is supported on `T ∩ Uᶜ`.
* `Stacks.DerivedQCoh.cohomologySupportedOn_derivedRestriction` — restriction to an open pulls
  the supporting set back.
* `Stacks.DerivedQCoh.isQuasicoherent_derivedRestriction` — restriction to an open subscheme
  preserves quasi-coherence of the cohomology sheaves.
* `Stacks.DerivedQCoh.isZero_quasicoherent_of_isZero_derivedInclusion` — the derived inclusion
  of the quasi-coherent modules detects the zero object.

## Implementation notes

The derived categories are the locally small ones of
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`: no `HasDerivedCategory` binder appears,
so instance search supplies `SheafOfModules.hasDerivedCategory` and
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, which are the same instance — the two
spellings `AlgebraicGeometry.Scheme.Modules X` and
`AlgebraicGeometry.SheafOfModules X.ringCatSheaf` of the category of `𝒪_X`-modules are
definitionally equal and so are these two instances. Fixing the model is what lets the dévissage be
combined with the affine case of [Stacks, Tag 06VT], which is available at this model alone.

Restriction to an open subspace is written `ExtensionByZeroModules.jStar`, the spelling the
closed-support substrate of
`StacksFrontier/Topology/Sheaves/Cohomology/SupportedComplexes/PushforwardAndRestriction.lean` uses;
`Stacks.Duality.OpenImmersion.jStar_eq_restrictFunctor` identifies it with Mathlib's restriction
along the inclusion of an open subscheme when the ambient ringed space is a scheme. Its
additivity and exactness are instance *arguments* rather than instances, because they are proved
by exhibiting adjoints on both sides and are not wanted in the instance cache.

## References

* [Stacks Project, Tag 09T6](https://stacks.math.columbia.edu/tag/09T6)
* [Stacks Project, Tag 08DF](https://stacks.math.columbia.edu/tag/08DF)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

-- `AlgebraicGeometry` also declares a `CohomologySupportedOn`; this file means the one of
-- `Stacks.Cohomology.PushforwardRestriction`, opened below, so the other is hidden here.
open AlgebraicGeometry hiding CohomologySupportedOn
open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated TopologicalSpace ExtensionByZeroModules ZeroObject
open Stacks.Cohomology.PushforwardRestriction
  (CohomologySupportedOn isZero_sheafOfModules_of_stalk_isZero
    isZero_jStar_obj_of_stalk_isZero isZero_derived_restrict_compl_of_supported)

universe u

namespace Stacks.DerivedQCoh

/-! ### Exactness of restriction to an open subspace -/

/-- **Restriction of modules to an open subspace is additive and exact.** It has extension by
zero as a left adjoint and direct image as a right adjoint, so it preserves all limits and all
colimits. All three are global instances (`ExtensionByZeroModules.jStar_additive`,
`jStar_preservesFiniteLimits`, `jStar_preservesFiniteColimits`); this bundled form is kept
because callers destructure it. -/
theorem jStar_additive_and_exact {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (U : Opens X) :
    (jStar U O).Additive ∧ PreservesFiniteLimits (jStar U O) ∧
      PreservesFiniteColimits (jStar U O) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

/-- **Direct image along an open immersion is additive**, being a right adjoint. -/
theorem jPush_additive {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (U : Opens X) :
    (jPush U O).Additive := by
  have : (jPush U O).IsRightAdjoint := (jStarAdjunction U O).isRightAdjoint
  exact Functor.additive_of_preserves_binary_products _

/-! ### Elementary properties of cohomological support -/

/-- Enlarging the allowed support preserves the cohomological support condition. -/
theorem cohomologySupportedOn_mono {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) {S T : Set X} (hST : S ⊆ T)
    {E : DerivedCategory (SheafOfModules.{u} O)} (hE : CohomologySupportedOn O S E) :
    CohomologySupportedOn O T E := fun i x hx => hE i x fun h => hx (hST h)

/-- **An object supported on the empty set is zero.** This is the base case of the finite
affine-cover induction: all stalks of all cohomology sheaves vanish, so all cohomology sheaves
vanish, so the object vanishes. -/
theorem isZero_of_cohomologySupportedOn_empty {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (E : DerivedCategory (SheafOfModules.{u} O))
    (hE : CohomologySupportedOn O (∅ : Set X) E) : IsZero E := by
  apply Stacks.SmallDerivedCategory.isZero_of_isZero_homologyFunctor_obj
  intro n
  apply isZero_sheafOfModules_of_stalk_isZero O
  intro x
  exact hE n x (by simp)

/-- If the restriction of an object to an open vanishes, its cohomology is supported on the
complement of that open. -/
theorem cohomologySupportedOn_compl_of_isZero_restrict {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (U : Opens X)
    (E : DerivedCategory (SheafOfModules.{u} O))
    [(jStar U O).Additive] [PreservesFiniteLimits (jStar U O)]
    [PreservesFiniteColimits (jStar U O)]
    (hE : IsZero ((jStar U O).mapDerivedCategory.obj E)) :
    CohomologySupportedOn O (Uᶜ : Set X) E := by
  intro i x hx
  let M : SheafOfModules.{u} O :=
    (DerivedCategory.homologyFunctor (SheafOfModules.{u} O) i).obj E
  have hHi : IsZero ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (resRing U O)) i).obj
      ((jStar U O).mapDerivedCategory.obj E)) :=
    Functor.map_isZero (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (resRing U O)) i) hE
  have hRestrict : IsZero ((jStar U O).obj M) :=
    hHi.of_iso ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
      (jStar U O) i).app E).symm
  let xU : U := ⟨x, by simpa using hx⟩
  have hS : IsZero ((SheafOfModules.toSheaf (resRing U O)).obj ((jStar U O).obj M)) :=
    Functor.map_isZero (SheafOfModules.toSheaf (resRing U O)) hRestrict
  have hStalk := (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero
    ((SheafOfModules.toSheaf (resRing U O)).obj ((jStar U O).obj M))).mp hS xU
  exact hStalk.of_iso (TopCat.Presheaf.stalkRestrictIso U M.val.presheaf xU).symm

/-- Support in a set and vanishing after restriction to an open cut the support down to the part
of that set outside the open. -/
theorem cohomologySupportedOn_inter_compl_of_isZero_restrict {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (T : Set X) (U : Opens X)
    (E : DerivedCategory (SheafOfModules.{u} O)) (hT : CohomologySupportedOn O T E)
    [(jStar U O).Additive] [PreservesFiniteLimits (jStar U O)]
    [PreservesFiniteColimits (jStar U O)]
    (hU : IsZero ((jStar U O).mapDerivedCategory.obj E)) :
    CohomologySupportedOn O (T ∩ (Uᶜ : Set X)) E := by
  have hC := cohomologySupportedOn_compl_of_isZero_restrict O U E hU
  intro i x hx
  by_cases hxT : x ∈ T
  · exact hC i x fun h => hx ⟨hxT, h⟩
  · exact hT i x hxT

/-- **The cone of a morphism which becomes invertible after restriction.** Let `f : E ⟶ F` be a
morphism of objects of `D(𝒪)` whose cohomology is supported on a closed set `T`, and suppose `f`
becomes an isomorphism after restriction to an open `U`. Then `f` fits into a distinguished
triangle whose third vertex is supported on `T ∩ Uᶜ`.

This is the dévissage step of [Stacks, Tag 09T6]: it is what removes one affine open from the
support at a time. -/
theorem exists_cocone_supportedOn_inter_compl {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (T : Set X) (hT : IsClosed T)
    (U : Opens X)
    (R : SheafOfModules.{u} O ⥤ SheafOfModules.{u} (resRing U O)) (hR : R = jStar U O)
    [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    {E F : DerivedCategory (SheafOfModules.{u} O)} (f : E ⟶ F)
    (hE : CohomologySupportedOn O T E) (hF : CohomologySupportedOn O T F)
    (hIso : IsIso (R.mapDerivedCategory.map f)) :
    ∃ (G : DerivedCategory (SheafOfModules.{u} O)) (g : F ⟶ G) (δ : G ⟶ E⟦(1 : ℤ)⟧),
      (Triangle.mk f g δ ∈ distTriang _) ∧
        CohomologySupportedOn O (T ∩ (Uᶜ : Set X)) G := by
  subst hR
  let V : Opens X := ⟨Tᶜ, hT.isOpen_compl⟩
  obtain ⟨hVadd, hVlim, hVcolim⟩ := jStar_additive_and_exact O V
  have := hVadd
  have := hVlim
  have := hVcolim
  obtain ⟨G, g, δ, hDist⟩ := distinguished_cocone_triangle f
  have hEV : IsZero ((jStar V O).mapDerivedCategory.obj E) :=
    isZero_derived_restrict_compl_of_supported O T hT E hE
  have hFV : IsZero ((jStar V O).mapDerivedCategory.obj F) :=
    isZero_derived_restrict_compl_of_supported O T hT F hF
  let Rv := (jStar V O).mapDerivedCategory
  let Ru := (jStar U O).mapDerivedCategory
  have hGV : IsZero (Rv.obj G) :=
    Triangle.isZero₃_of_isZero₁₂ (Rv.mapTriangle.obj (Triangle.mk f g δ))
      (Rv.map_distinguished _ hDist) hEV hFV
  have hGU : IsZero (Ru.obj G) :=
    Triangle.isZero₃_of_isIso₁ (Ru.mapTriangle.obj (Triangle.mk f g δ))
      (Ru.map_distinguished _ hDist) hIso
  have hGT : CohomologySupportedOn O T G := by
    have h := cohomologySupportedOn_compl_of_isZero_restrict O V G hGV
    intro i x hx
    exact h i x (by simpa [V] using hx)
  exact ⟨G, g, δ, hDist,
    cohomologySupportedOn_inter_compl_of_isZero_restrict O T U G hGT hGU⟩

/-! ### Restriction to an open subscheme -/

/-- **Restriction to an open pulls the supporting set back.** If the cohomology of `E` is
supported on `T ⊆ X`, the cohomology of its restriction to an open `U` is supported on the
preimage of `T` in `U`. -/
theorem cohomologySupportedOn_derivedRestriction {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (U : Opens X) (T : Set X)
    (R : SheafOfModules.{u} O ⥤ SheafOfModules.{u} (resRing U O)) (hR : R = jStar U O)
    [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (E : DerivedCategory (SheafOfModules.{u} O)) (hE : CohomologySupportedOn O T E) :
    CohomologySupportedOn (resRing U O) (Subtype.val ⁻¹' T)
      (R.mapDerivedCategory.obj E) := by
  subst hR
  intro n x hx
  exact (hE n x.1 hx).of_iso
    (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).mapIso
      ((toAb (resRing U O)).mapIso
        ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
          (jStar U O) n).app E))) ≪≫
      TopCat.Presheaf.stalkRestrictIso U
        (((DerivedCategory.homologyFunctor _ n).obj E).val.presheaf) x)

/-- **Restriction to an open subscheme preserves quasi-coherent cohomology.** Restriction is
exact, so it commutes with the cohomology sheaves, and it carries a quasi-coherent module to a
quasi-coherent module. -/
theorem isQuasicoherent_derivedRestriction (X : Scheme.{u}) (U : X.Opens)
    (R : SheafOfModules.{u} X.ringCatSheaf ⥤
      SheafOfModules.{u} (resRing U X.ringCatSheaf))
    (hR : R = jStar U X.ringCatSheaf)
    [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (E : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf))
    (hE : DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent X.ringCatSheaf) E) :
    DerivedCategoryB.derivedCategoryB
        (A := SheafOfModules.{u} U.toScheme.ringCatSheaf)
        (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf)
      (R.mapDerivedCategory.obj E) := by
  subst hR
  intro n
  let M : X.Modules :=
    (DerivedCategory.homologyFunctor (SheafOfModules.{u} X.ringCatSheaf) n).obj E
  have : M.IsQuasicoherent := hE n
  have hM : ((jStar U X.ringCatSheaf).obj M).IsQuasicoherent := by
    rw [Stacks.Duality.OpenImmersion.jStar_eq_restrictFunctor X U]
    exact Scheme.Modules.isQuasicoherent_restrictFunctor U.ι M
  exact (SheafOfModules.isQuasicoherent.{u} U.toScheme.ringCatSheaf).prop_of_iso
    ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
      (jStar U X.ringCatSheaf) n).app E).symm hM

/-- **The derived inclusion of the quasi-coherent modules detects the zero object.** The
inclusion is exact and faithful, so it commutes with the cohomology objects and reflects their
vanishing. -/
theorem isZero_quasicoherent_of_isZero_derivedInclusion (X : Scheme.{u})
    (A : DerivedCategory (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory)
    (hA : IsZero (((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι).mapDerivedCategory.obj A)) :
    IsZero A := by
  let I := (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι
  apply Stacks.SmallDerivedCategory.isZero_of_isZero_homologyFunctor_obj
  intro n
  have hz : IsZero (I.obj ((DerivedCategory.homologyFunctor _ n).obj A)) :=
    (Functor.map_isZero (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} X.ringCatSheaf) n) hA).of_iso
      ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso I n).app A).symm
  apply (IsZero.iff_id_eq_zero _).2
  apply I.map_injective
  simpa using (IsZero.iff_id_eq_zero _).1 hz

/-! ### The finite affine-cover induction -/

/-- A quasi-compact scheme is covered by finitely many affine opens, in the indexing form the
support induction consumes. -/
theorem exists_finite_affine_open_cover (X : Scheme.{u}) [CompactSpace X] :
    ∃ (ι : Type u) (_ : Fintype ι) (U : ι → X.Opens),
      (∀ i, IsAffineOpen (U i)) ∧ (⨆ i, U i) = ⊤ := by
  obtain ⟨s, hs, hcover⟩ :=
    (isCompact_iff_finite_and_eq_biUnion_affineOpens (X := X) (U := ⊤)).mp isCompact_univ
  have : Fintype s := hs.fintype
  refine ⟨s, inferInstance, fun i => (i.1 : X.Opens), fun i => i.1.2, le_antisymm le_top ?_⟩
  intro x hx
  have hxV : x ∈ ⋃ V ∈ s, (V : X.Opens) := by
    have hxTop : x ∈ (⊤ : X.Opens) := Set.mem_univ x
    rw [hcover] at hxTop
    simpa only [Opens.mem_iSup, Set.mem_iUnion, SetLike.mem_coe] using hxTop
  rcases Set.mem_iUnion.mp hxV with ⟨V, hxV⟩
  rcases Set.mem_iUnion.mp hxV with ⟨hV, hxV⟩
  exact Opens.mem_iSup.mpr ⟨⟨V, hV⟩, hxV⟩

/-- **Induction on the number of affine opens needed to cover the support.** Let `X` be a
quasi-compact scheme and let `P`, `Q` be properties of objects of `D(𝒪_X)`. Suppose `P` holds at
every zero object, `P` at the two outer vertices of a distinguished triangle implies `P` at the
first vertex, and for every affine open `U`, every closed `S` and every `E` satisfying `Q` and
supported on `S` there is a distinguished triangle starting at `E` whose middle vertex satisfies
`P` and whose third vertex satisfies `Q` and is supported on `S \ U`. Then `P` holds at every
object satisfying `Q`.

Finitely many affine opens cover `X`; removing them from the support one at a time, the support
is empty after the last step and the object is zero. -/
theorem property_of_finite_affine_support (X : Scheme.{u}) [CompactSpace X]
    (P Q : ObjectProperty (DerivedCategory (SheafOfModules.{u} X.ringCatSheaf)))
    (hzero : ∀ E, IsZero E → P E)
    (htri : ∀ (T : Triangle (DerivedCategory (SheafOfModules.{u} X.ringCatSheaf))),
      T ∈ distTriang _ → P T.obj₂ → P T.obj₃ → P T.obj₁)
    (hstep : ∀ (U : X.Opens), IsAffineOpen U → ∀ (S : Set X), IsClosed S → ∀ E, Q E →
      CohomologySupportedOn X.ringCatSheaf S E →
        ∃ (T : Triangle (DerivedCategory (SheafOfModules.{u} X.ringCatSheaf))),
          T.obj₁ = E ∧ T ∈ distTriang _ ∧ P T.obj₂ ∧ Q T.obj₃ ∧
            CohomologySupportedOn X.ringCatSheaf (S \ U) T.obj₃) :
    ∀ E, Q E → P E := by
  classical
  have hs : ∀ (s : Finset X.Opens), (∀ U ∈ s, IsAffineOpen U) →
      ∀ (S : Set X), IsClosed S → S ⊆ ⋃ U ∈ s, (U : Set X) →
        ∀ E, Q E → CohomologySupportedOn X.ringCatSheaf S E → P E := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro _ S _ hSE E _ hE
        have hS0 : S ⊆ ∅ := by simpa using hSE
        exact hzero E (isZero_of_cohomologySupportedOn_empty X.ringCatSheaf E
          (cohomologySupportedOn_mono X.ringCatSheaf hS0 hE))
    | @insert U s _ ih =>
        intro ha S hS hSE E hQE hE
        obtain ⟨T, hTE, hT, hP, hQ, hSupp⟩ := hstep U (ha U (by simp)) S hS E hQE hE
        have hrem : S \ (U : Set X) ⊆ ⋃ V ∈ s, (V : Set X) := by
          intro x hx
          obtain ⟨V, hV, hxV⟩ := Set.mem_iUnion₂.mp (hSE hx.1)
          rcases Finset.mem_insert.mp hV with rfl | hV
          · exact (hx.2 hxV).elim
          · exact Set.mem_iUnion₂.mpr ⟨V, hV, hxV⟩
        have hP3 := ih (fun V hV => ha V (Finset.mem_insert_of_mem hV)) (S \ (U : Set X))
          (hS.inter U.isOpen.isClosed_compl) hrem T.obj₃ hQ hSupp
        exact hTE ▸ htri T hT hP hP3
  obtain ⟨ι, hι, U, hU, hcover⟩ := exists_finite_affine_open_cover X
  have := hι
  intro E hE
  refine hs (Finset.univ.image U) (fun V hV => ?_) Set.univ isClosed_univ ?_ E hE ?_
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hV
    exact hU i
  · intro x _
    have hx : x ∈ ⨆ i, U i := by rw [hcover]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    exact Set.mem_iUnion₂.mpr ⟨U i, Finset.mem_image.mpr ⟨i, by simp, rfl⟩, hi⟩
  · intro n x hx
    exact (hx (Set.mem_univ x)).elim

end Stacks.DerivedQCoh

end
