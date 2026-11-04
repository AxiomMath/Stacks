module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import StacksFrontier.AlgebraicGeometry.General.Basic
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.OpenImmersionRegular
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.Defs
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.RegularSchemes
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.SmoothTarget
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.NoetherianRegularKoszul
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.PerfectFactor
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.SmoothPermanence
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleBasics.NormalCrossings.SmoothPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.RegularImmersionComposition
public import StacksFrontier.RingTheory.DividedPowers.CompleteIntersection.RegularSequenceTFAE
import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.ImmersionIntoSmooth

/-!
# A perfect morphism out of a local complete intersection over a Noetherian base

Let `X ⟶ Y ⟶ S` be a commutative triangle of morphisms of schemes with `S` locally Noetherian
and `Y ⟶ S` locally of finite type.  If `X ⟶ Y` is perfect and `X ⟶ S` is a local complete
intersection morphism, then `X ⟶ Y` is a local complete intersection morphism, and `Y ⟶ S` is
Koszul at the image of every point of `X`.

## Main results

* `AlgebraicGeometry.isLocalCompleteIntersectionMorphism_of_perfect`: the relative conclusion of
  Stacks 09RL.
* `AlgebraicGeometry.koszulAt_of_perfect`: its conclusion on the base.

## Implementation notes

Near a point `x` the local complete intersection structure of `X ⟶ S` gives a Koszul-regular
immersion `i : U₀ ⟶ P` of a neighbourhood of `x` into a scheme smooth over `S`, and the finite
type hypothesis on `Y ⟶ S` gives an affine open `V ∋ f x` over an affine open `W ⊆ S` together
with a closed immersion `V ⟶ 𝔸(n; W)` into affine space, which is smooth over `S`.  The ambient
scheme of the argument is the fibre product `E = 𝔸(n; W) ×_S P`, smooth over both factors, and
its closed subscheme `Q = E ×_{𝔸(n; W)} V`, which is smooth over `V`.  On `U = U₀ ⊓ f⁻¹V` the
induced morphism `U ⟶ Q` composed with `Q ⟶ E` is Koszul-regular by Stacks 067S, because its
composite with the smooth projection `E ⟶ P` is `i`, and it is perfect by Stacks 068D, because
its composite with the smooth morphism `Q ⟶ Y` is the restriction of `f`.  Stacks 09RK then makes
`U ⟶ Q` a regular immersion, which gives the first conclusion, and makes `Q ⟶ E` regular near the
image of `U`.

The kernel of `Q ⟶ E` on local rings is the extension of the kernel of `V ⟶ 𝔸(n; W)` along the
flat local homomorphism induced by `E ⟶ 𝔸(n; W)`
(`AlgebraicGeometry.ker_stalkMap_pullback_fst`), so faithfully flat descent of Koszul-regular
ideals, Stacks 068N, returns a regular sequence generating the kernel of `V ⟶ 𝔸(n; W)` at the
image point.  The regular locus of an immersion into a locally Noetherian scheme is open, which
turns that one point into a neighbourhood and gives the second conclusion.

Regular and Koszul-regular immersions are interchanged throughout by Stacks 063L, available
because every scheme in sight is locally Noetherian; this is where the hypothesis that `S` be
locally Noetherian is used, and it is the role played in the source by Stacks 09CC.

## References

* [Stacks Project, Lemma 37.62.12 (09RL)](https://stacks.math.columbia.edu/tag/09RL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.RegularIdealSheaf
open Stacks.Flatness.RegularSequenceQuotient

universe u

namespace AlgebraicGeometry

/-- Koszul-regularity of an immersion transfers along an equality of morphisms. -/
private theorem isKoszulRegularImmersion_congr {Z T : Scheme.{u}} {i j : Z ⟶ T}
    [IsImmersion i] [IsImmersion j] (hij : i = j) (hi : IsKoszulRegularImmersion i) :
    IsKoszulRegularImmersion j := by
  subst hij; exact hi

/-- Regularity of an immersion transfers along an equality of morphisms. -/
private theorem isRegularImmersion_congr {Z T : Scheme.{u}} {i j : Z ⟶ T}
    [IsImmersion i] [IsImmersion j] (hij : i = j) (hi : IsRegularImmersion i) :
    IsRegularImmersion j := by
  subst hij; exact hi

/-- An open immersion on the source does not change the kernel of a map of local rings, since the
stalk map of an open immersion is an isomorphism. -/
private theorem ker_stalkMap_comp_of_isOpenImmersion {Z' Z T : Scheme.{u}} (a : Z' ⟶ Z)
    [IsOpenImmersion a] (m : Z ⟶ T) (z : Z') :
    RingHom.ker ((a ≫ m).stalkMap z).hom = RingHom.ker (m.stalkMap (a.base z)).hom := by
  have hcomp : ((a ≫ m).stalkMap z).hom
      = (a.stalkMap z).hom.comp (m.stalkMap (a.base z)).hom := by
    rw [Scheme.Hom.stalkMap_comp]; rfl
  have hinj : Function.Injective (a.stalkMap z).hom :=
    (asIso (a.stalkMap z)).commRingCatIsoToRingEquiv.injective
  rw [hcomp]
  exact RingHom.ker_comp_of_injective _ hinj

/-- Regular generators of the stalk kernel of a morphism at a point of an open subscheme on
which it restricts to a regular immersion. -/
private theorem exists_isRegular_ker_stalkMap_of_mem_opens {Z T : Scheme.{u}} (O : Z.Opens)
    (m : Z ⟶ T) [IsImmersion (O.ι ≫ m)] (hO : IsRegularImmersion (O.ι ≫ m)) (z : Z)
    (hz : z ∈ O) :
    ∃ rs : List (T.presheaf.stalk (m.base z)),
      RingTheory.Sequence.IsRegular (T.presheaf.stalk (m.base z)) rs ∧
        Ideal.ofList rs = RingHom.ker (m.stalkMap z).hom := by
  obtain ⟨rs, hrs, hspan⟩ := exists_isRegular_ker_stalkMap_of_isRegularImmersion (O.ι ≫ m) hO
    (⟨z, hz⟩ : O.toScheme)
  exact ⟨rs, hrs, hspan.trans (ker_stalkMap_comp_of_isOpenImmersion O.ι m (⟨z, hz⟩ : O.toScheme))⟩

/-- Regular generators of the kernel of `ψ` are obtained from regular generators of the kernel of
`e ≫ ψ`, for an isomorphism `e`, by transporting the sequence along `e`. -/
private theorem exists_isRegular_ker_of_iso_comp {A B C : CommRingCat.{u}} (e : A ≅ B)
    (ψ : B ⟶ C)
    (hA : ∃ rs : List A, RingTheory.Sequence.IsRegular A rs ∧
      Ideal.ofList rs = RingHom.ker (e.hom ≫ ψ).hom) :
    ∃ rs : List B, RingTheory.Sequence.IsRegular B rs ∧
      Ideal.ofList rs = RingHom.ker ψ.hom := by
  obtain ⟨rs, hrs, hspan⟩ := hA
  have hsurj : Function.Surjective e.hom.hom := fun b =>
    ⟨e.inv.hom b, ConcreteCategory.congr_hom e.inv_hom_id b⟩
  refine ⟨rs.map e.hom.hom, ?_, ?_⟩
  · exact (isRegular_ringEquiv_congr e.commRingCatIsoToRingEquiv rs).mp hrs
  · rw [← Ideal.map_ofList, hspan, CommRingCat.hom_comp, ← RingHom.comap_ker,
      Ideal.map_comap_of_surjective _ hsurj]

/-- **The local step of Stacks 09RL.**  Suppose given a commutative triangle `X ⟶ Y ⟶ S` with
`S` locally Noetherian, `Y ⟶ S` locally of finite type and `f : X ⟶ Y` perfect, a point `x` of
`X` lying in an open `U₀` that admits a Koszul-regular immersion `i₀` into a scheme `P` smooth
over `S` and compatible with `X ⟶ S`, and an open `V ∋ f x` of `Y` that admits a closed immersion
`iY` into a scheme `A` smooth over `S` and compatible with `Y ⟶ S`.  Then `f` is Koszul at `x`
and `g` is Koszul at `f x`. -/
private theorem koszulAt_and_koszulAt_image_aux {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    {h : X ⟶ S} (hcomm : f ≫ g = h) [IsLocallyNoetherian S] [LocallyOfFiniteType g]
    [AlgebraicGeometry.Perfect f] {U₀ : X.Opens} {P : Scheme.{u}} (i₀ : U₀.toScheme ⟶ P)
    (π₀ : P ⟶ S) [IsImmersion i₀] [Smooth π₀] (hi₀kos : IsKoszulRegularImmersion i₀)
    (hfac : U₀.ι ≫ h = i₀ ≫ π₀) {V : Y.Opens} {A : Scheme.{u}} (iY : V.toScheme ⟶ A)
    (aS : A ⟶ S) [IsClosedImmersion iY] [Smooth aS] (hiYover : iY ≫ aS = V.ι ≫ g)
    (x : X) (hxU₀ : x ∈ U₀) (hxV : f.base x ∈ V) :
    KoszulAt f x ∧ KoszulAt g (f.base x) := by
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian π₀
  have : IsLocallyNoetherian A := LocallyOfFiniteType.isLocallyNoetherian aS
  -- The smooth ambient scheme `E = A ×_S P` and its closed subscheme `Q = E ×_A V`.
  set ρ : pullback aS π₀ ⟶ A := pullback.fst aS π₀ with hρdef
  set σ : pullback aS π₀ ⟶ P := pullback.snd aS π₀ with hσdef
  have : Smooth ρ := inferInstanceAs (Smooth (pullback.fst aS π₀))
  have : Smooth σ := inferInstanceAs (Smooth (pullback.snd aS π₀))
  have : IsLocallyNoetherian (pullback aS π₀) := LocallyOfFiniteType.isLocallyNoetherian ρ
  set cQ : pullback ρ iY ⟶ pullback aS π₀ := pullback.fst ρ iY with hcQdef
  set dQ : pullback ρ iY ⟶ V.toScheme := pullback.snd ρ iY with hdQdef
  have : IsClosedImmersion cQ := inferInstanceAs (IsClosedImmersion (pullback.fst ρ iY))
  have : Smooth dQ := inferInstanceAs (Smooth (pullback.snd ρ iY))
  have : IsLocallyNoetherian (pullback ρ iY) := LocallyOfFiniteType.isLocallyNoetherian cQ
  -- The neighbourhood of `x` on which everything is defined, and the maps out of it.
  have hUU₀ : U₀ ⊓ f ⁻¹ᵁ V ≤ U₀ := inf_le_left
  have hUV : U₀ ⊓ f ⁻¹ᵁ V ≤ f ⁻¹ᵁ V := inf_le_right
  set U : X.Opens := U₀ ⊓ f ⁻¹ᵁ V with hUdef
  have hxU : x ∈ U := ⟨hxU₀, hxV⟩
  set fU : U.toScheme ⟶ V.toScheme := f.resLE V U hUV with hfUdef
  have hfUι : fU ≫ V.ι = U.ι ≫ f := Scheme.Hom.resLE_comp_ι f _
  have hUh : U.ι ≫ h = (X.homOfLE hUU₀ ≫ i₀) ≫ π₀ := by
    rw [Category.assoc, ← hfac, ← Category.assoc, X.homOfLE_ι]
  have hcompat : (fU ≫ iY) ≫ aS = (X.homOfLE hUU₀ ≫ i₀) ≫ π₀ := by
    rw [← hUh, Category.assoc, hiYover, ← Category.assoc, hfUι, Category.assoc, hcomm]
  set α : U.toScheme ⟶ pullback aS π₀ :=
    pullback.lift (fU ≫ iY) (X.homOfLE hUU₀ ≫ i₀) hcompat with hαdef
  have hαρ : α ≫ ρ = fU ≫ iY := pullback.lift_fst _ _ _
  have hασ : α ≫ σ = X.homOfLE hUU₀ ≫ i₀ := pullback.lift_snd _ _ _
  set jU : U.toScheme ⟶ pullback ρ iY := pullback.lift α fU hαρ with hjUdef
  have hjc : jU ≫ cQ = α := pullback.lift_fst _ _ _
  have hjd : jU ≫ dQ = fU := pullback.lift_snd _ _ _
  -- The restriction of `i₀` is Koszul-regular, hence so is `α`, by Stacks 067S.
  have hiUkos : IsKoszulRegularImmersion (X.homOfLE hUU₀ ≫ i₀) :=
    Stacks.AlgebraicGeometry.isKoszulRegularImmersion_comp _ i₀
      (Stacks.AlgebraicGeometry.RegularIdealSheaf.isKoszulRegularImmersion_of_isOpenImmersion
        (X.homOfLE hUU₀)) hi₀kos
  have hαimσ : IsImmersion (α ≫ σ) := by rw [hασ]; infer_instance
  have hαim : IsImmersion α := IsImmersion.of_comp α σ
  have hαkos : IsKoszulRegularImmersion α :=
    isKoszulRegularImmersion_of_comp_of_smooth α σ
      (isKoszulRegularImmersion_congr hασ.symm hiUkos)
  have hαreg : IsRegularImmersion α :=
    (isRegularImmersion_iff_isKoszulRegularImmersion α).mpr hαkos
  -- `jU` is perfect, by Stacks 068D, hence a regular immersion, by Stacks 09RK.
  have hjimc : IsImmersion (jU ≫ cQ) := by rw [hjc]; infer_instance
  have hjim : IsImmersion jU := IsImmersion.of_comp jU cQ
  have hjfac : jU ≫ (dQ ≫ V.ι) = U.ι ≫ f := by rw [← Category.assoc, hjd, hfUι]
  have : AlgebraicGeometry.Perfect (U.ι ≫ f) := inferInstance
  have : Smooth (dQ ≫ V.ι) := inferInstance
  have : AlgebraicGeometry.Perfect jU := perfect_of_comp_eq_of_smooth jU (dQ ≫ V.ι) hjfac
  have hjcα : IsRegularImmersion (jU ≫ cQ) := isRegularImmersion_congr hjc.symm hαreg
  have hjreg : IsRegularImmersion jU := isRegularImmersion_of_perfect jU cQ hjcα
  have hjkos : IsKoszulRegularImmersion jU :=
    (isRegularImmersion_iff_isKoszulRegularImmersion jU).mp hjreg
  refine ⟨⟨finiteTypeAt_of_locallyOfFiniteType f x, U, hxU, pullback ρ iY, jU, dQ ≫ V.ι, hjim,
    hjkos, inferInstance, hjfac.symm⟩, finiteTypeAt_of_locallyOfFiniteType g (f.base x), ?_⟩
  -- The point of `Q` above `x` and its images.
  set u : U.toScheme := ⟨x, hxU⟩ with hudef
  set q := jU.base u with hqdef
  have hdq : dQ.base q = fU.base u :=
    congrArg (fun k : U.toScheme ⟶ V.toScheme => k.base u) hjd
  have hVdq : V.ι.base (dQ.base q) = f.base x := by
    rw [hdq]
    exact congrArg (fun k : U.toScheme ⟶ Y => k.base u) hfUι
  -- Stacks 09RK makes `cQ` regular near the image of `jU`, so its kernel on local rings at `q`
  -- is generated by a regular sequence.
  obtain ⟨Oq, hOq, hOqreg⟩ := exists_opens_isRegularImmersion_comp_of_perfect jU cQ hjcα
  have hkerc := exists_isRegular_ker_stalkMap_of_mem_opens Oq cQ hOqreg q (hOq u)
  -- The kernel of `cQ` on local rings is the extension of the kernel of `iY`.
  have hpt : ρ.base (cQ.base q) = iY.base (dQ.base q) :=
    congrArg (fun k : pullback ρ iY ⟶ A => k.base q) pullback.condition
  have hker : RingHom.ker (cQ.stalkMap q).hom
      = Ideal.map (ρ.stalkMap (cQ.base q)).hom
        (RingHom.ker ((eqToHom (congrArg A.presheaf.stalk hpt) ≫
          iY.stalkMap (dQ.base q)).hom)) := ker_stalkMap_pullback_fst ρ iY q
  -- Faithfully flat descent along the flat local homomorphism induced by `ρ`.
  let : Algebra (A.presheaf.stalk (ρ.base (cQ.base q)))
      ((pullback aS π₀).presheaf.stalk (cQ.base q)) := (ρ.stalkMap (cQ.base q)).hom.toAlgebra
  have halg : (algebraMap (A.presheaf.stalk (ρ.base (cQ.base q)))
      ((pullback aS π₀).presheaf.stalk (cQ.base q))) = (ρ.stalkMap (cQ.base q)).hom :=
    RingHom.algebraMap_toAlgebra _
  have : Module.Flat (A.presheaf.stalk (ρ.base (cQ.base q)))
      ((pullback aS π₀).presheaf.stalk (cQ.base q)) := Flat.stalkMap ρ (cQ.base q)
  have : IsLocalHom (algebraMap (A.presheaf.stalk (ρ.base (cQ.base q)))
      ((pullback aS π₀).presheaf.stalk (cQ.base q))) := by
    rw [halg]
    exact inferInstanceAs (IsLocalHom (ρ.stalkMap (cQ.base q)).hom)
  set ψ : A.presheaf.stalk (ρ.base (cQ.base q)) ⟶ V.toScheme.presheaf.stalk (dQ.base q) :=
    eqToHom (congrArg A.presheaf.stalk hpt) ≫ iY.stalkMap (dQ.base q) with hψdef
  have hψne : RingHom.ker ψ.hom ≠ ⊤ := by
    intro htop
    have h1 : (1 : A.presheaf.stalk (ρ.base (cQ.base q))) ∈ RingHom.ker ψ.hom := by
      rw [htop]; trivial
    rw [RingHom.mem_ker, map_one] at h1
    exact one_ne_zero h1
  have hdesc := Stacks.CompleteIntersection.exists_regularSequence_of_map_of_flat_local
    (R := A.presheaf.stalk (ρ.base (cQ.base q)))
    (S := (pullback aS π₀).presheaf.stalk (cQ.base q))
    (RingHom.ker ψ.hom) hψne (by rw [halg, ← hker]; exact hkerc)
  -- Transport across the identification of the two names of the local ring of `A`.
  have hkeriY : ∃ rs : List (A.presheaf.stalk (iY.base (dQ.base q))),
      RingTheory.Sequence.IsRegular (A.presheaf.stalk (iY.base (dQ.base q))) rs ∧
        Ideal.ofList rs = RingHom.ker (iY.stalkMap (dQ.base q)).hom :=
    exists_isRegular_ker_of_iso_comp (eqToIso (congrArg A.presheaf.stalk hpt))
      (iY.stalkMap (dQ.base q)) hdesc
  -- The regular locus of `iY` is open, so the single point spreads to a neighbourhood.
  set Vr : V.toScheme.Opens :=
    ⟨regularStalkLocus iY, isOpen_regularStalkLocus iY⟩ with hVrdef
  have hdqVr : dQ.base q ∈ Vr := hkeriY
  have hVrreg : IsRegularImmersion (Vr.ι ≫ iY) :=
    isRegularImmersion_of_exists_isRegular_ker_stalkMap (Vr.ι ≫ iY) fun v => by
      rw [ker_stalkMap_comp_of_isOpenImmersion]
      exact v.2
  have hVrkos : IsKoszulRegularImmersion (Vr.ι ≫ iY) :=
    (isRegularImmersion_iff_isKoszulRegularImmersion (Vr.ι ≫ iY)).mp hVrreg
  -- Transport the neighbourhood from `V` to `Y` and assemble.
  refine ⟨V.ι ''ᵁ Vr, ⟨dQ.base q, hdqVr, hVdq⟩, A,
    (V.ι.isoImage Vr).inv ≫ (Vr.ι ≫ iY), aS, inferInstance, ?_, inferInstance, ?_⟩
  · exact Stacks.AlgebraicGeometry.isKoszulRegularImmersion_iso_hom_comp
      (V.ι.isoImage Vr).symm (Vr.ι ≫ iY) hVrkos
  · rw [Category.assoc, Category.assoc, hiYover, ← Category.assoc Vr.ι V.ι g,
      ← Category.assoc, Scheme.Hom.isoImage_inv_ι]

/-- **The local content of Stacks 09RL.**  At every point `x` of `X` the morphism `f : X ⟶ Y` is
Koszul at `x`, and `g : Y ⟶ S` is Koszul at `f x`. -/
private theorem koszulAt_and_koszulAt_image {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    {h : X ⟶ S} (hcomm : f ≫ g = h) [IsLocallyNoetherian S] [LocallyOfFiniteType g]
    [AlgebraicGeometry.Perfect f] (hh : IsLocalCompleteIntersectionMorphism h) (x : X) :
    KoszulAt f x ∧ KoszulAt g (f.base x) := by
  obtain ⟨-, U₀, hxU₀, P, i₀, π₀, hi₀, hi₀kos, hπ₀, hfac⟩ := hh x
  have := hi₀
  have : Smooth π₀ := hπ₀
  -- Affine charts `V ⊆ Y` over `W ⊆ S` around `f x`.
  obtain ⟨_, ⟨W, hW, rfl⟩, hhxW, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (g.base (f.base x))) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hfxV, hVW⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (show f.base x ∈ ((g ⁻¹ᵁ W : Y.Opens) : Set Y) from hhxW) (g ⁻¹ᵁ W).2
  have : IsAffine (Scheme.Opens.toScheme W) := hW
  have : IsAffine (Scheme.Opens.toScheme V) := hV
  have : IsLocallyNoetherian (Scheme.Opens.toScheme W) :=
    isLocallyNoetherian_of_isOpenImmersion (Scheme.Opens.ι W)
  -- A closed immersion of `V` into affine space over `W`.
  have hVW' : V ≤ g ⁻¹ᵁ W := hVW
  have : LocallyOfFiniteType (g.resLE W V hVW') := by
    delta Scheme.Hom.resLE; infer_instance
  have : LocallyOfFinitePresentation (g.resLE W V hVW') :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  obtain ⟨n, iY, hiYcl, hiYover⟩ :=
    Stacks.AlgebraicGeometry.Tag05JXGeneral.exists_closedImmersion_affineSpace_of_lfp
      (g.resLE W V hVW')
  have := hiYcl
  have : Smooth (AffineSpace (ULift.{u} (Fin n)) (Scheme.Opens.toScheme W) ↘
      Scheme.Opens.toScheme W) := AffineSpace.smooth_over _ _
  refine koszulAt_and_koszulAt_image_aux f g hcomm i₀ π₀ hi₀kos hfac iY
    ((AffineSpace (ULift.{u} (Fin n)) (Scheme.Opens.toScheme W) ↘ Scheme.Opens.toScheme W) ≫
      Scheme.Opens.ι W) ?_ x hxU₀ hfxV
  rw [← Category.assoc, hiYover, Scheme.Hom.resLE_comp_ι]

/-- **Stacks 09RL, the relative conclusion.**  Let `X ⟶ Y ⟶ S` be a commutative triangle of
morphisms of schemes with `S` locally Noetherian and `Y ⟶ S` locally of finite type.  If
`f : X ⟶ Y` is perfect and `X ⟶ S` is a local complete intersection morphism, then `f` is a local
complete intersection morphism. -/
@[stacks 09RL "the morphism to the intermediate scheme is a local complete intersection morphism"]
theorem isLocalCompleteIntersectionMorphism_of_perfect {X Y S : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ S) {h : X ⟶ S} (hcomm : f ≫ g = h) [IsLocallyNoetherian S] [LocallyOfFiniteType g]
    [AlgebraicGeometry.Perfect f] (hh : IsLocalCompleteIntersectionMorphism h) :
    IsLocalCompleteIntersectionMorphism f :=
  fun x => (koszulAt_and_koszulAt_image f g hcomm hh x).1

/-- **Stacks 09RL, the conclusion on the base.**  In the same situation, `g : Y ⟶ S` is Koszul at
the image of every point of `X`. -/
@[stacks 09RL "the intermediate scheme is Koszul over the base at every point of the image"]
theorem koszulAt_of_perfect {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) {h : X ⟶ S}
    (hcomm : f ≫ g = h) [IsLocallyNoetherian S] [LocallyOfFiniteType g]
    [AlgebraicGeometry.Perfect f] (hh : IsLocalCompleteIntersectionMorphism h) (x : X) :
    KoszulAt g (f.base x) :=
  (koszulAt_and_koszulAt_image f g hcomm hh x).2

end AlgebraicGeometry

end
