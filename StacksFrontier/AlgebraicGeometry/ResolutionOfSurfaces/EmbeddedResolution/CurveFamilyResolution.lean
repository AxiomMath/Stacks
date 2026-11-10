module

public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.AmbientCurveResolution
public import StacksFrontier.Topology.Dimension.DimensionLEOne
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Separating finitely many embedded curves by blowing up closed points

Let `Y 1, …, Y n` be pairwise distinct one-dimensional integral closed subschemes of a Noetherian
scheme `X`, each satisfying the equivalent conditions of [Stacks, Tag 0BI4]. Then a finite chain
of blowups of `X` at closed points makes their strict transforms pairwise disjoint regular
curves. The simultaneous transport of the whole family along one chain is recorded by the
relation `AlgebraicGeometry.FamilyTransform`.

## Main definitions

* `AlgebraicGeometry.FamilyTransform` relates a chain of blowups of the ambient scheme at closed
  points to the successive strict transforms of a finite family of closed subschemes along it.

## Main results

* `AlgebraicGeometry.exists_pointBlowupChain_familyTransform_isRegular_pairwise_disjoint`:
  [Stacks, Tag 0BI8].
* `AlgebraicGeometry.FamilyTransform.chainTransform`: each member of the family is transported
  by `AlgebraicGeometry.ChainTransform` along the same chain.
* `AlgebraicGeometry.FamilyTransform.trans`: simultaneous transports compose.
* `AlgebraicGeometry.exists_familyTransform_of_pointBlowupChain`: every chain of blowups at
  closed points carries every finite family.
* `AlgebraicGeometry.exists_familyTransform_isRegular`: the family form of [Stacks, Tag 0BI5] —
  one distinguished member of the family becomes a regular curve.

## Implementation notes

`AlgebraicGeometry.ChainTransform` is not functional in its ideal-sheaf argument: both of its
constructors can apply to one composite morphism, since blowing up an already Cartier closed
point is an isomorphism. One member's strict transform can therefore not be recovered from a
chain produced by a lemma about another member, so the whole family is carried at once, and that
is what every induction below consumes.

The proof is the one in the source. [Stacks, Tag 0BI5] in its family form makes one member a
regular curve at a time; a regular curve is unchanged by a further blowup at a closed point by
[Stacks, Tag 0BI7] part (1), so the members already resolved stay resolved, and the conditions
of [Stacks, Tag 0BI4] are inherited by a strict transform because a resolution of singularities
of a curve factors through any blowup of it in an ideal sheaf with proper support. Two distinct
regular curves are then separated by induction on the number of their intersection points and,
inside that, on the intersection multiplicity of [Stacks, Tag 0BI6] at one of them, which
[Stacks, Tag 0BI7] part (3) lowers.

## References

* [Stacks Project, Tag 0BI8](https://stacks.math.columbia.edu/tag/0BI8)
* [Stacks Project, Tag 0BI7](https://stacks.math.columbia.edu/tag/0BI7)
* [Stacks Project, Tag 0BI6](https://stacks.math.columbia.edu/tag/0BI6)
* [Stacks Project, Tag 0BI5](https://stacks.math.columbia.edu/tag/0BI5)
* [Stacks Project, Tag 0BI4](https://stacks.math.columbia.edu/tag/0BI4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.ResolutionOfSurfaces Stacks.Topology.Dimension

universe u

namespace AlgebraicGeometry

/-! ### Simultaneous strict transforms along a chain of point blowups -/

/-- The successive strict transforms of a finite family `Y : Fin n → X.IdealSheafData` of closed
subschemes of `X` along a chain of blowups of `X` at closed points, indexed by the composite
morphism to `X`: `FamilyTransform Y f J` says that `f : W ⟶ X` is such a chain and that `J i` is
the ideal sheaf of the strict transform of `Y i` in `W`, for every `i`. -/
public inductive FamilyTransform {X : Scheme.{u}} {n : ℕ} (Y : Fin n → X.IdealSheafData) :
    {W : Scheme.{u}} → (W ⟶ X) → (Fin n → W.IdealSheafData) → Prop
  | refl : FamilyTransform Y (𝟙 X) Y
  | step {W : Scheme.{u}} {f : W ⟶ X} {J : Fin n → W.IdealSheafData}
      (hJ : FamilyTransform Y f J) (w : W) (hw : IsClosed ({w} : Set W)) :
      FamilyTransform Y (blowUpToBase (centerIdeal w hw) ≫ f)
        (fun i => transformIdeal (J i) w hw)

/-- Each member of a family carried along a chain of point blowups is carried along that same
chain by `AlgebraicGeometry.ChainTransform`. -/
public theorem FamilyTransform.chainTransform {X W : Scheme.{u}} {n : ℕ}
    {Y : Fin n → X.IdealSheafData} {f : W ⟶ X} {J : Fin n → W.IdealSheafData}
    (h : FamilyTransform Y f J) (i : Fin n) : ChainTransform (Y i) f (J i) := by
  induction h with
  | refl => exact .refl
  | step hJ w hw ih => exact ih.step w hw

/-- A simultaneous chain of strict transforms lies over a chain of blowups at closed points. -/
public theorem FamilyTransform.pointBlowupChain {X W : Scheme.{u}} {n : ℕ}
    {Y : Fin n → X.IdealSheafData} {f : W ⟶ X} {J : Fin n → W.IdealSheafData}
    (h : FamilyTransform Y f J) : PointBlowupChain X Set.univ W f := by
  induction h with
  | refl => exact .refl
  | step hJ w hw ih => exact ih.step w hw (Set.mem_univ _)

/-- Simultaneous strict transports compose: transporting a family to `W` and then transporting
the resulting family to `V` transports the original family to `V`. -/
public theorem FamilyTransform.trans {X W V : Scheme.{u}} {n : ℕ}
    {Y : Fin n → X.IdealSheafData} {f : W ⟶ X} {J : Fin n → W.IdealSheafData}
    (hJ : FamilyTransform Y f J) {g : V ⟶ W} {K : Fin n → V.IdealSheafData}
    (hK : FamilyTransform J g K) : FamilyTransform Y (g ≫ f) K := by
  induction hK with
  | refl => simpa using hJ
  | step hK' w hw ih =>
      rw [Category.assoc]
      exact ih.step w hw

/-- **Every chain of blowups at closed points carries every finite family of closed
subschemes.** The centres are read off the chain and the family is transformed at each. -/
public theorem exists_familyTransform_of_pointBlowupChain {X W : Scheme.{u}} {n : ℕ}
    (Y : Fin n → X.IdealSheafData) {f : W ⟶ X} (h : PointBlowupChain X Set.univ W f) :
    ∃ J : Fin n → W.IdealSheafData, FamilyTransform Y f J := by
  induction h with
  | refl => exact ⟨Y, .refl⟩
  | step hh w hw _ ih =>
      obtain ⟨J, hJ⟩ := ih
      exact ⟨_, hJ.step w hw⟩

/-! ### Transport along isomorphisms -/

/-- A closed subscheme of a Noetherian scheme is Noetherian. -/
private theorem isNoetherian_subscheme {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) : IsNoetherian I.subscheme := by
  have : IsLocallyNoetherian I.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian I.subschemeι
  have : CompactSpace I.subscheme := I.subschemeι.isClosedEmbedding.compactSpace
  constructor

/-- Isomorphic schemes have the same topological Krull dimension. -/
private theorem topologicalKrullDim_eq_of_iso {A B : Scheme.{u}} (e : A ≅ B) :
    topologicalKrullDim A = topologicalKrullDim B :=
  IsHomeomorph.topologicalKrullDim_eq e.hom (Scheme.homeoOfIso e).isHomeomorph

/-- Regularity transports along an isomorphism of schemes. -/
private theorem isRegular_of_isIso {A B : Scheme.{u}} (f : A ⟶ B) [IsIso f]
    (hB : IsRegular B) : IsRegular A := fun x => by
  obtain ⟨U, hx, hU⟩ := hB (f x)
  refine ⟨⟨f ⁻¹ᵁ U.1, U.2.preimage_of_isIso f⟩, hx, ?_⟩
  let : IsRegularRing Γ(B, U.1) := hU
  exact IsRegularRing.of_ringEquiv (asIso (f.app U.1)).commRingCatIsoToRingEquiv

/-! ### Lifting a chain of point blowups of one member to the ambient scheme -/

/-- A chain of blowups of the closed subscheme cut out by one member of a family at closed
points is the simultaneous chain of strict transforms of the whole family along a chain of
blowups of the ambient scheme at closed points. -/
private theorem exists_familyTransform_of_pointBlowupChain_subscheme {X V : Scheme.{u}} {n : ℕ}
    (Y : Fin n → X.IdealSheafData) (i : Fin n) {g : V ⟶ (Y i).subscheme}
    (t : PointBlowupChain (Y i).subscheme Set.univ V g) :
    ∃ (W : Scheme.{u}) (f : W ⟶ X) (J : Fin n → W.IdealSheafData),
      FamilyTransform Y f J ∧ Nonempty (V ≅ (J i).subscheme) := by
  induction t with
  | refl => exact ⟨X, 𝟙 X, Y, .refl, ⟨Iso.refl _⟩⟩
  | @step V g t v hv _ ih =>
      obtain ⟨W, f, J, hJ, ⟨e⟩⟩ := ih
      -- Transport the centre to the ambient scheme through the strict transform.
      have hq : IsClosed ({e.hom v} : Set (J i).subscheme) := by
        have h₁ : IsClosed ((Scheme.homeoOfIso e) '' ({v} : Set V)) :=
          (Scheme.homeoOfIso e).isClosedMap _ hv
        rw [Set.image_singleton] at h₁
        exact h₁
      have hw : IsClosed ({(J i).subschemeι (e.hom v)} : Set W) := by
        simpa only [Set.image_singleton] using (J i).subschemeι.isClosedEmbedding.isClosedMap _ hq
      obtain ⟨d⟩ := nonempty_transformIdeal_subscheme_iso_blowUp (J i) (e.hom v) hq hw
      obtain ⟨b⟩ := nonempty_blowUp_comap_iso_of_isIso e.hom (centerIdeal (e.hom v) hq)
      rw [comap_centerIdeal_of_isClosedImmersion e.hom v hv hq] at b
      exact ⟨blowUp (centerIdeal ((J i).subschemeι (e.hom v)) hw),
        blowUpToBase (centerIdeal ((J i).subschemeι (e.hom v)) hw) ≫ f,
        fun k => transformIdeal (J k) ((J i).subschemeι (e.hom v)) hw,
        hJ.step _ hw, ⟨b ≪≫ d.symm⟩⟩

/-! ### Resolving one member of a family -/

/-- **The family form of [Stacks, Tag 0BI5].** Let `X` be a Noetherian scheme, let
`Y : Fin n → X.IdealSheafData` be a finite family of closed subschemes, and let `Y i` be
integral of dimension one and admit an alteration by a regular scheme — one of the equivalent
conditions of [Stacks, Tag 0BI4]. Then there is a finite chain of blowups of `X` at closed
points along which the strict transform of `Y i` becomes a regular curve, and which carries the
whole family simultaneously. -/
public theorem exists_familyTransform_isRegular_of_pointBlowupChain {X : Scheme.{u}}
    [IsNoetherian X] {n : ℕ} (Y : Fin n → X.IdealSheafData) (i : Fin n)
    (hYint : IsIntegral (Y i).subscheme) (hYdim : topologicalKrullDim (Y i).subscheme = 1)
    (hY : ∃ (V : Scheme.{u}) (g : V ⟶ (Y i).subscheme),
      PointBlowupChain (Y i).subscheme Set.univ V g ∧ IsRegular V) :
    ∃ (W : Scheme.{u}) (f : W ⟶ X) (J : Fin n → W.IdealSheafData),
      FamilyTransform Y f J ∧ IsIntegral (J i).subscheme ∧
        topologicalKrullDim (J i).subscheme = 1 ∧ IsRegular (J i).subscheme := by
  have := hYint
  have := isNoetherian_subscheme (Y i)
  obtain ⟨V, g, t, hVreg⟩ := hY
  obtain ⟨W, f, J, hJ, ⟨e⟩⟩ := exists_familyTransform_of_pointBlowupChain_subscheme Y i t
  obtain ⟨-, hVint, -, -⟩ := pointBlowupChain_properties hYdim t
  have : IsIntegral V := hVint
  refine ⟨W, f, J, hJ, IsIntegral.of_isIso e.hom, ?_, fun x => ?_⟩
  · rw [← topologicalKrullDim_eq_of_iso e]
    exact topologicalKrullDim_eq_of_pointBlowupChain hYdim t
  · exact isRegular_of_isIso e.inv hVreg x

/-- **The family form of [Stacks, Tag 0BI5].** Let `X` be a Noetherian scheme, let
`Y : Fin n → X.IdealSheafData` be a finite family of closed subschemes, and let `Y i` be
integral of dimension one and admit an alteration by a regular scheme — one of the equivalent
conditions of [Stacks, Tag 0BI4]. Then there is a finite chain of blowups of `X` at closed
points along which the strict transform of `Y i` becomes a regular curve, and which carries the
whole family simultaneously. -/
public theorem exists_familyTransform_isRegular {X : Scheme.{u}} [IsNoetherian X] {n : ℕ}
    (Y : Fin n → X.IdealSheafData) (i : Fin n) [IsIntegral (Y i).subscheme]
    (hYdim : topologicalKrullDim (Y i).subscheme = 1)
    (hY : ∃ (Z : Scheme.{u}) (g : Z ⟶ (Y i).subscheme), IsAlteration g ∧ IsRegular Z) :
    ∃ (W : Scheme.{u}) (f : W ⟶ X) (J : Fin n → W.IdealSheafData),
      FamilyTransform Y f J ∧ IsIntegral (J i).subscheme ∧
        topologicalKrullDim (J i).subscheme = 1 ∧ IsRegular (J i).subscheme := by
  have := isNoetherian_subscheme (Y i)
  exact exists_familyTransform_isRegular_of_pointBlowupChain Y i inferInstance hYdim
    (((resolveCurve_tfae (Y i).subscheme hYdim).out 1 3).mp hY)

/-! ### Closed points of a closed subscheme -/

/-- A subsingleton space is not one-dimensional. -/
private theorem false_of_subsingleton_of_topologicalKrullDim_eq_one (T : Type*)
    [TopologicalSpace T] [Subsingleton T] (h : topologicalKrullDim T = 1) : False := by
  have hzero := topologicalKrullDim_zero_of_discreteTopology T
  rw [h] at hzero
  exact (by norm_num : ¬ (1 : WithBot ℕ∞) ≤ 0) hzero

/-- A point of a closed subscheme lying over a closed point of the ambient scheme is closed. -/
private theorem isClosed_singleton_of_subschemeι_eq {X : Scheme.{u}} (I : X.IdealSheafData)
    {p : X} (hp : IsClosed ({p} : Set X)) (y : I.subscheme) (hy : I.subschemeι y = p) :
    IsClosed ({y} : Set I.subscheme) := by
  have h : ({y} : Set I.subscheme) = I.subschemeι ⁻¹' {p} := by
    ext x
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    exact ⟨fun hx => hx ▸ hy,
      fun hx => I.subschemeι.isClosedEmbedding.injective (hx.trans hy.symm)⟩
  rw [h]
  exact hp.preimage I.subschemeι.continuous

/-! ### A point blowup off the subscheme does not change it -/

/-- A morphism restricting to an isomorphism over the whole target is an isomorphism. -/
private theorem isIso_of_morphismRestrict_top {A B : Scheme.{u}} (f : A ⟶ B)
    [IsIso (f ∣_ ⊤)] : IsIso f := by
  have : IsIso ((⊤ : B.Opens).ι) := inferInstanceAs (IsIso B.topIso.hom)
  have h := morphismRestrict_ι f ⊤
  have : IsIso ((f ⁻¹ᵁ ⊤).ι ≫ f) := h ▸ inferInstance
  have : IsIso (f ⁻¹ᵁ ⊤).ι := by
    change IsIso ((⊤ : A.Opens).ι)
    exact inferInstanceAs (IsIso A.topIso.hom)
  exact IsIso.of_isIso_comp_left (f ⁻¹ᵁ ⊤).ι f

/-- The blowup in an ideal sheaf cutting out the empty subscheme is an isomorphism. -/
private theorem isIso_blowUpToBase_of_support_eq_bot {X : Scheme.{u}} (I : X.IdealSheafData)
    (hI : I.support = ⊥) : IsIso (blowUpToBase I) := by
  have h := isIso_blowUp_restrict_compl_support I
  have hU : (⟨I.supportᶜ, I.support.isClosed.isOpen_compl⟩ : X.Opens) = ⊤ := by
    ext x
    simp [hI]
  rw [hU] at h
  exact isIso_of_morphismRestrict_top _

/-- The strict transform maps to the subscheme through the blowup of the inverse image of the
centre. -/
private theorem strictTransformBlowUpIso_hom_comp_blowUpToBase {X : Scheme.{u}}
    (I : X.IdealSheafData) (p : X) (hp : IsClosed ({p} : Set X)) :
    ((Over.forget I.subscheme).mapIso
      (strictTransformBlowUpIso I.subschemeι (centerIdeal p hp))).hom ≫
      blowUpToBase ((centerIdeal p hp).comap I.subschemeι) = transformToCurve I p hp :=
  Over.w (strictTransformBlowUpIso I.subschemeι (centerIdeal p hp)).hom

/-- If the blowup of the inverse image centre is an isomorphism, the strict transform of a
closed subscheme is the subscheme itself: [Stacks, Tag 080E] identifies the strict transform
with that blowup over the subscheme. -/
@[sga "7 X 2.6" "special case"]
private theorem transformToCurve_isIso_of_isIso_blowUpToBase {X : Scheme.{u}}
    (I : X.IdealSheafData) (p : X) (hp : IsClosed ({p} : Set X))
    (h : IsIso (blowUpToBase ((centerIdeal p hp).comap I.subschemeι))) :
    IsIso (transformToCurve I p hp) := by
  rw [← strictTransformBlowUpIso_hom_comp_blowUpToBase]
  exact IsIso.comp_isIso' (Iso.isIso_hom _) h

/-- **A blowup at a closed point outside a closed subscheme does not change it.** -/
private theorem transformToCurve_isIso_of_notMem_support {X : Scheme.{u}}
    (I : X.IdealSheafData) (p : X) (hp : IsClosed ({p} : Set X)) (hIp : p ∉ I.support) :
    IsIso (transformToCurve I p hp) := by
  refine transformToCurve_isIso_of_isIso_blowUpToBase I p hp
    (isIso_blowUpToBase_of_support_eq_bot _ ?_)
  rw [Scheme.IdealSheafData.support_comap]
  refine SetLike.coe_injective ?_
  change I.subschemeι ⁻¹' ((centerIdeal p hp).support : Set X) = (∅ : Set I.subscheme)
  rw [show ((centerIdeal p hp).support : Set X) = {p} from
    Scheme.IdealSheafData.coe_support_vanishingIdeal _]
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
  exact fun h => hIp (h ▸ x.property)

/-- The closed subscheme cut out by the strict transform is isomorphic to the strict transform. -/
private theorem nonempty_transformIdeal_subscheme_iso_transform {X : Scheme.{u}}
    (I : X.IdealSheafData) (p : X) (hp : IsClosed ({p} : Set X)) :
    Nonempty ((transformIdeal I p hp).subscheme ≅ transform I p hp) :=
  have : IsClosedImmersion (transformToBlowUp I p hp) :=
    isClosedImmersion_transformToBlowUp I p hp
  ⟨(asIso (transformToBlowUp I p hp).toImage).symm⟩

/-- When the strict transform maps isomorphically to the subscheme, the closed subscheme it
cuts out in the ambient blowup is isomorphic to the original subscheme. -/
private theorem nonempty_transformIdeal_subscheme_iso_self {X : Scheme.{u}}
    (I : X.IdealSheafData) (p : X) (hp : IsClosed ({p} : Set X))
    (h : IsIso (transformToCurve I p hp)) :
    Nonempty ((transformIdeal I p hp).subscheme ≅ I.subscheme) := by
  obtain ⟨e₁⟩ := nonempty_transformIdeal_subscheme_iso_transform I p hp
  have := h
  exact ⟨e₁ ≪≫ asIso (transformToCurve I p hp)⟩

/-! ### One point blowup preserves a one-dimensional integral closed subscheme -/

/-- **The blowup of a one-dimensional integral Noetherian scheme at a closed point is again
one-dimensional and integral**: it is a one-step chain of blowups at closed points. -/
private theorem isIntegral_and_topologicalKrullDim_blowUp_centerIdeal {Y : Scheme.{u}}
    [IsIntegral Y] [IsNoetherian Y] (hdim : topologicalKrullDim Y = 1) (y : Y)
    (hy : IsClosed ({y} : Set Y)) :
    IsIntegral (blowUp (centerIdeal y hy)) ∧
      topologicalKrullDim (blowUp (centerIdeal y hy)) = 1 := by
  have hchain : PointBlowupChain Y Set.univ (blowUp (centerIdeal y hy))
      (blowUpToBase (centerIdeal y hy) ≫ 𝟙 Y) :=
    PointBlowupChain.refl.step y hy (Set.mem_univ _)
  obtain ⟨-, hint, -, -⟩ := pointBlowupChain_properties hdim hchain
  exact ⟨hint, topologicalKrullDim_eq_of_pointBlowupChain hdim hchain⟩

/-- **One blowup of a Noetherian scheme at a closed point leaves a one-dimensional integral
closed subscheme one-dimensional and integral.** At a point of the subscheme the strict
transform is the blowup of the subscheme at the point above it, by [Stacks, Tag 080E]; away from
the subscheme nothing changes. -/
private theorem transformIdeal_integral_curve {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) [IsIntegral I.subscheme]
    (hdim : topologicalKrullDim I.subscheme = 1) (p : X) (hp : IsClosed ({p} : Set X)) :
    IsIntegral (transformIdeal I p hp).subscheme ∧
      topologicalKrullDim (transformIdeal I p hp).subscheme = 1 := by
  have : IsNoetherian I.subscheme := isNoetherian_subscheme I
  by_cases hIp : p ∈ I.support
  · obtain ⟨y, rfl⟩ : ∃ y : I.subscheme, I.subschemeι y = p := ⟨⟨p, hIp⟩, rfl⟩
    have hy : IsClosed ({y} : Set I.subscheme) :=
      isClosed_singleton_of_subschemeι_eq I hp y rfl
    obtain ⟨d⟩ := nonempty_transformIdeal_subscheme_iso_blowUp I y hy hp
    obtain ⟨hint, hdim'⟩ := isIntegral_and_topologicalKrullDim_blowUp_centerIdeal hdim y hy
    have : IsIntegral (blowUp (centerIdeal y hy)) := hint
    exact ⟨IsIntegral.of_isIso d.inv, (topologicalKrullDim_eq_of_iso d).trans hdim'⟩
  · obtain ⟨e⟩ := nonempty_transformIdeal_subscheme_iso_self I p hp
      (transformToCurve_isIso_of_notMem_support I p hp hIp)
    exact ⟨IsIntegral.of_isIso e.inv, (topologicalKrullDim_eq_of_iso e).trans hdim⟩

/-- **A blowup at a closed point does not change a regular one-dimensional integral closed
subscheme.** On the subscheme the centre is an effective Cartier divisor, so [Stacks, Tag 0BI7]
part (1) applies; off the subscheme nothing changes. -/
private theorem transformToCurve_isIso_of_isRegular {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) [IsIntegral I.subscheme]
    (hdim : topologicalKrullDim I.subscheme = 1) (hreg : IsRegular I.subscheme)
    (p : X) (hp : IsClosed ({p} : Set X)) : IsIso (transformToCurve I p hp) := by
  have hstalk : IsLocallyNoetherian I.subscheme ∧
      ∀ z : I.subscheme, IsRegularLocalRing (I.subscheme.presheaf.stalk z) :=
    ((isRegular_tfae I.subscheme).out 1 2).mp hreg
  by_cases hIp : p ∈ I.support
  · exact strictTransformToCurve_isIso I hdim p hp ⟨p, hIp⟩ rfl (hstalk.2 _)
  · exact transformToCurve_isIso_of_notMem_support I p hp hIp

/-- **One blowup at a closed point leaves a regular one-dimensional integral closed subscheme
a regular one-dimensional integral closed subscheme**, isomorphic to the original. -/
private theorem transformIdeal_regular_curve {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) [IsIntegral I.subscheme]
    (hdim : topologicalKrullDim I.subscheme = 1) (hreg : IsRegular I.subscheme)
    (p : X) (hp : IsClosed ({p} : Set X)) :
    IsIntegral (transformIdeal I p hp).subscheme ∧
      topologicalKrullDim (transformIdeal I p hp).subscheme = 1 ∧
      IsRegular (transformIdeal I p hp).subscheme := by
  obtain ⟨e⟩ := nonempty_transformIdeal_subscheme_iso_self I p hp
    (transformToCurve_isIso_of_isRegular I hdim hreg p hp)
  exact ⟨IsIntegral.of_isIso e.inv, (topologicalKrullDim_eq_of_iso e).trans hdim,
    isRegular_of_isIso e.hom hreg⟩

/-! ### Distinct one-dimensional integral closed subschemes -/

/-- **Neither of two distinct one-dimensional integral closed subschemes contains the other.**
Containment would make the smaller one a proper irreducible closed subset of the larger, hence
a point, contradicting its dimension. -/
private theorem support_not_le_of_ne {X : Scheme.{u}} (I J : X.IdealSheafData)
    [IsIntegral I.subscheme] [IsIntegral J.subscheme]
    (hdimI : topologicalKrullDim I.subscheme = 1)
    (hdimJ : topologicalKrullDim J.subscheme = 1) (hne : I ≠ J) : ¬ I.support ≤ J.support := by
  intro hle
  have : IrreducibleSpace I.subscheme := irreducibleSpace_of_isIntegral I.subscheme
  have : IrreducibleSpace J.subscheme := irreducibleSpace_of_isIntegral J.subscheme
  let k : I.subscheme → J.subscheme := fun x => ⟨x.1, hle x.2⟩
  have hk : Continuous k := I.subschemeι.continuous.subtype_mk _
  have hS : IsClosed (J.subschemeι ⁻¹' (I.support : Set X)) :=
    I.support.isClosed.preimage J.subschemeι.continuous
  have hrange : Set.range k = J.subschemeι ⁻¹' (I.support : Set X) := by
    ext y
    exact ⟨fun ⟨x, hx⟩ => hx ▸ x.2, fun hy => ⟨⟨y.1, hy⟩, Subtype.ext rfl⟩⟩
  have hirr : IsIrreducible (J.subschemeι ⁻¹' (I.support : Set X)) := by
    rw [← hrange, ← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ I.subscheme).image k hk.continuousOn
  have hproper : J.subschemeι ⁻¹' (I.support : Set X) ≠ Set.univ := by
    intro h
    refine hne (eq_of_support_eq I J (le_antisymm hle fun x hx => ?_))
    exact show (⟨x, hx⟩ : J.subscheme) ∈ J.subschemeι ⁻¹' (I.support : Set X) from
      h ▸ Set.mem_univ _
  have hsub := subsingleton_of_isIrreducible_of_ne_univ hdimJ.le hS hirr hproper
  have : Subsingleton I.subscheme := ⟨fun x y => Subtype.ext (congrArg
    (fun z : J.subscheme => z.1) (hsub (hrange ▸ Set.mem_range_self x)
      (hrange ▸ Set.mem_range_self y)))⟩
  exact false_of_subsingleton_of_topologicalKrullDim_eq_one I.subscheme hdimI

/-- The support of a distinct one-dimensional integral closed subscheme `J` does not pull back to
the whole of `I`. -/
private theorem preimage_support_ne_univ {X : Scheme.{u}} (I J : X.IdealSheafData)
    [IsIntegral I.subscheme] [IsIntegral J.subscheme]
    (hdimI : topologicalKrullDim I.subscheme = 1)
    (hdimJ : topologicalKrullDim J.subscheme = 1) (hne : I ≠ J) :
    I.subschemeι ⁻¹' (J.support : Set X) ≠ Set.univ := by
  intro h
  refine support_not_le_of_ne I J hdimI hdimJ hne fun x hx => ?_
  exact show (⟨x, hx⟩ : I.subscheme) ∈ I.subschemeι ⁻¹' (J.support : Set X) from
    h ▸ Set.mem_univ _

/-- **Two distinct one-dimensional integral closed subschemes of a Noetherian scheme meet in a
finite set.** -/
private theorem finite_inter_support {X : Scheme.{u}} [IsNoetherian X] (I J : X.IdealSheafData)
    [IsIntegral I.subscheme] [IsIntegral J.subscheme]
    (hdimI : topologicalKrullDim I.subscheme = 1)
    (hdimJ : topologicalKrullDim J.subscheme = 1) (hne : I ≠ J) :
    ((I.support : Set X) ∩ J.support).Finite := by
  have : IsNoetherian I.subscheme := isNoetherian_subscheme I
  have : IrreducibleSpace I.subscheme := irreducibleSpace_of_isIntegral I.subscheme
  have hS : IsClosed (I.subschemeι ⁻¹' (J.support : Set X)) :=
    J.support.isClosed.preimage I.subschemeι.continuous
  have hproper := preimage_support_ne_univ I J hdimI hdimJ hne
  have hfinite := finite_of_isClosed_of_ne_univ hdimI.le hS hproper
  have himage : I.subschemeι '' (I.subschemeι ⁻¹' (J.support : Set X)) =
      (I.support : Set X) ∩ J.support := by
    ext x
    exact ⟨fun ⟨y, hy, hyx⟩ => hyx ▸ ⟨y.2, hy⟩, fun ⟨hxI, hxJ⟩ => ⟨⟨x, hxI⟩, hxJ, rfl⟩⟩
  exact himage ▸ hfinite.image I.subschemeι

/-- **A point on two distinct one-dimensional integral closed subschemes is closed.** -/
private theorem isClosed_singleton_of_mem_inter_support {X : Scheme.{u}}
    (I J : X.IdealSheafData) [IsIntegral I.subscheme] [IsIntegral J.subscheme]
    (hdimI : topologicalKrullDim I.subscheme = 1)
    (hdimJ : topologicalKrullDim J.subscheme = 1) (hne : I ≠ J)
    (p : X) (hpI : p ∈ I.support) (hpJ : p ∈ J.support) : IsClosed ({p} : Set X) := by
  have : IrreducibleSpace I.subscheme := irreducibleSpace_of_isIntegral I.subscheme
  have hS : IsClosed (I.subschemeι ⁻¹' (J.support : Set X)) :=
    J.support.isClosed.preimage I.subschemeι.continuous
  have hproper := preimage_support_ne_univ I J hdimI hdimJ hne
  have hpoint := isClosed_singleton_of_mem_of_ne_univ hdimI.le hS hproper
    (x := (⟨p, hpI⟩ : I.subscheme)) hpJ
  have hset : I.subschemeι.base '' ({(⟨p, hpI⟩ : I.subscheme)} : Set I.subscheme) = {p} :=
    Set.image_singleton
  exact hset ▸ I.subschemeι.isClosedEmbedding.isClosedMap _ hpoint

/-- The generic point of a one-dimensional integral closed subscheme does not lie on a distinct
one. -/
private theorem genericPoint_notMem_support_of_ne {X : Scheme.{u}} (I J : X.IdealSheafData)
    [IsIntegral I.subscheme] [IsIntegral J.subscheme]
    (hdimI : topologicalKrullDim I.subscheme = 1)
    (hdimJ : topologicalKrullDim J.subscheme = 1) (hne : I ≠ J)
    (η : I.subscheme) (hη : η ∈ genericPoints I.subscheme) : I.subschemeι η ∉ J.support := by
  have : IrreducibleSpace I.subscheme := irreducibleSpace_of_isIntegral I.subscheme
  have hgeneric : IsGenericPoint η Set.univ := by
    change closure {η} = Set.univ
    simpa only [genericPoints, Set.mem_ofPred_eq, irreducibleComponents_eq_singleton,
      Set.mem_singleton_iff] using hη
  intro hmem
  have hsubset := (hgeneric.mem_closed_set_iff
    (J.support.isClosed.preimage I.subschemeι.continuous)).mp hmem
  exact support_not_le_of_ne I J hdimI hdimJ hne fun x hx =>
    hsubset (Set.mem_univ (⟨x, hx⟩ : I.subscheme))

/-! ### The intersection multiplicity of two distinct curves -/

/-- A point lies in the support of a sum of ideal sheaves iff it lies in both supports. -/
private theorem mem_support_sup_iff {X : Scheme.{u}} {I J : X.IdealSheafData} {p : X} :
    p ∈ (I ⊔ J).support ↔ p ∈ I.support ∧ p ∈ J.support := by
  rw [Scheme.IdealSheafData.support_sup]
  exact Iff.rfl

/-- The standing situation of [Stacks, Tag 0BI6] at a point of the intersection of two distinct
one-dimensional integral closed subschemes of a locally Noetherian scheme. -/
private def intersectionContext {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I J : X.IdealSheafData) [IsIntegral I.subscheme] [IsIntegral J.subscheme]
    (hdimI : topologicalKrullDim I.subscheme = 1)
    (hdimJ : topologicalKrullDim J.subscheme = 1) (hne : I ≠ J)
    (p : X) (hp : p ∈ (I ⊔ J).support) : IntersectionMultiplicityContext.{u} where
  X := X
  locallyNoetherian := inferInstance
  y := I
  z := J
  integralY := inferInstance
  dimensionY := hdimI
  p := p
  p_mem_intersection := hp
  p_isClosed := by
    have hp' := mem_support_sup_iff.mp hp
    exact isClosed_singleton_of_mem_inter_support I J hdimI hdimJ hne p hp'.1 hp'.2
  genericPoint_not_mem := genericPoint_notMem_support_of_ne I J hdimI hdimJ hne

/-- **The intersection multiplicity of two distinct curves at a point of their intersection is
positive.** -/
private theorem intersectionLength_pos {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I J : X.IdealSheafData) [IsIntegral I.subscheme] [IsIntegral J.subscheme]
    (hdimI : topologicalKrullDim I.subscheme = 1)
    (hdimJ : topologicalKrullDim J.subscheme = 1) (hne : I ≠ J)
    (p : X) (hp : p ∈ (I ⊔ J).support) : 0 < intersectionLength I J p hp := by
  have h : (0 : ℕ∞) <
      ((intersectionContext I J hdimI hdimJ hne p hp).intersectionMultiplicity : ℕ∞) := by
    rw [IntersectionMultiplicityContext.intersectionMultiplicity_natCast_eq_length]
    exact Module.length_pos
  exact (mod_cast h : 0 < (intersectionContext I J hdimI hdimJ hne p hp).intersectionMultiplicity)

/-! ### Supports of strict transforms -/

/-- The strict transform sits over the subscheme it transforms. -/
private theorem transformToBlowUp_comp_blowUpToBase {X : Scheme.{u}} (I : X.IdealSheafData)
    (p : X) (hp : IsClosed ({p} : Set X)) :
    transformToBlowUp I p hp ≫ blowUpToBase (centerIdeal p hp) =
      transformToCurve I p hp ≫ I.subschemeι := by
  change ((strictTransformCenterIdeal I p hp).subschemeι ≫
      pullback.snd I.subschemeι (blowUpToBase (centerIdeal p hp))) ≫
      blowUpToBase (centerIdeal p hp) =
    ((strictTransformCenterIdeal I p hp).subschemeι ≫
      pullback.fst I.subschemeι (blowUpToBase (centerIdeal p hp))) ≫ I.subschemeι
  rw [Category.assoc, Category.assoc, pullback.condition]

/-- The support of the strict transform is the range of its closed immersion into the ambient
blowup. -/
private theorem coe_transformIdeal_support {X : Scheme.{u}} (I : X.IdealSheafData)
    (p : X) (hp : IsClosed ({p} : Set X)) :
    ((transformIdeal I p hp).support : Set (blowUp (centerIdeal p hp))) =
      Set.range (transformToBlowUp I p hp).base := by
  have : IsClosedImmersion (transformToBlowUp I p hp) :=
    isClosedImmersion_transformToBlowUp I p hp
  rw [show transformIdeal I p hp = (transformToBlowUp I p hp).ker from rfl,
    Scheme.Hom.support_ker,
    (transformToBlowUp I p hp).isClosedEmbedding.isClosed_range.closure_eq]

/-- The strict transform lies over the subscheme. -/
private theorem transformIdeal_support_subset {X : Scheme.{u}} (I : X.IdealSheafData)
    (p : X) (hp : IsClosed ({p} : Set X)) :
    ((transformIdeal I p hp).support : Set (blowUp (centerIdeal p hp))) ⊆
      (blowUpToBase (centerIdeal p hp)).base ⁻¹' (I.support : Set X) := by
  rw [coe_transformIdeal_support]
  rintro _ ⟨z, rfl⟩
  have h := congrArg (fun f => f z) (transformToBlowUp_comp_blowUpToBase I p hp)
  simp only [Scheme.Hom.comp_apply] at h
  change (blowUpToBase (centerIdeal p hp)) (transformToBlowUp I p hp z) ∈ (I.support : Set X)
  rw [h]
  exact (transformToCurve I p hp z).property

/-- The image of the support of the strict transform in the ambient scheme is the image of the
range of the map to the subscheme. -/
private theorem image_transformIdeal_support {X : Scheme.{u}} (I : X.IdealSheafData)
    (p : X) (hp : IsClosed ({p} : Set X)) :
    (blowUpToBase (centerIdeal p hp)).base '' ((transformIdeal I p hp).support : Set _) =
      I.subschemeι.base '' Set.range (transformToCurve I p hp).base := by
  rw [coe_transformIdeal_support, ← Set.range_comp, ← Set.range_comp]
  refine congrArg Set.range (funext fun z => ?_)
  have h := congrArg (fun f => f z) (transformToBlowUp_comp_blowUpToBase I p hp)
  simpa only [Scheme.Hom.comp_apply, Function.comp_apply] using h

/-- **When the strict transform covers the subscheme, the image of its support is the support of
the subscheme.** -/
private theorem image_transformIdeal_support_eq {X : Scheme.{u}} (I : X.IdealSheafData)
    (p : X) (hp : IsClosed ({p} : Set X))
    (hsurj : Function.Surjective (transformToCurve I p hp).base) :
    (blowUpToBase (centerIdeal p hp)).base '' ((transformIdeal I p hp).support : Set _) =
      (I.support : Set X) := by
  rw [image_transformIdeal_support, hsurj.range_eq, Set.image_univ, I.range_subschemeι]

/-- When the strict transform maps injectively to the subscheme, the blowup map is injective on
the support of the strict transform. -/
private theorem injOn_blowUpToBase_transformIdeal_support {X : Scheme.{u}}
    (I : X.IdealSheafData) (p : X) (hp : IsClosed ({p} : Set X))
    (hinj : Function.Injective (transformToCurve I p hp).base) :
    Set.InjOn (blowUpToBase (centerIdeal p hp)).base
      ((transformIdeal I p hp).support : Set _) := by
  rw [coe_transformIdeal_support]
  rintro _ ⟨z, rfl⟩ _ ⟨w, rfl⟩ h
  have hz := congrArg (fun f => f z) (transformToBlowUp_comp_blowUpToBase I p hp)
  have hw := congrArg (fun f => f w) (transformToBlowUp_comp_blowUpToBase I p hp)
  simp only [Scheme.Hom.comp_apply] at hz hw
  exact congrArg (transformToBlowUp I p hp).base
    (hinj (I.subschemeι.isClosedEmbedding.injective (hz.symm.trans (h.trans hw))))

/-- Disjointness of closed subsets is disjointness of the underlying sets. -/
private theorem disjoint_closeds_iff {T : Type*} [TopologicalSpace T] (A B : Closeds T) :
    Disjoint A B ↔ Disjoint (A : Set T) (B : Set T) := by
  simp [disjoint_iff, ← SetLike.coe_set_eq]

/-- **Disjoint closed subschemes have disjoint strict transforms.** -/
private theorem disjoint_transformIdeal_support {X : Scheme.{u}} (I J : X.IdealSheafData)
    (hIJ : Disjoint I.support J.support) (p : X) (hp : IsClosed ({p} : Set X)) :
    Disjoint (transformIdeal I p hp).support (transformIdeal J p hp).support := by
  rw [disjoint_closeds_iff] at hIJ ⊢
  exact (hIJ.preimage _).mono (transformIdeal_support_subset I p hp)
    (transformIdeal_support_subset J p hp)

/-! ### Surjectivity of the map from the strict transform -/

/-- **The blowup of an integral Noetherian scheme in an ideal sheaf with proper support is
surjective**: it is proper, and an isomorphism over the dense complement of the support. -/
@[ega "II 8.1.4" "(ii), special case"]
private theorem surjective_blowUpToBase_of_support_ne_univ {Y : Scheme.{u}} [IsNoetherian Y]
    [IsIntegral Y] (ℐ : Y.IdealSheafData) (hproper : (ℐ.support : Set Y) ≠ Set.univ) :
    Function.Surjective (blowUpToBase ℐ).base := by
  have : IrreducibleSpace Y := irreducibleSpace_of_isIntegral Y
  have hUne : ((ℐ.support.compl : Y.Opens) : Set Y).Nonempty := by
    by_contra h
    refine hproper (Set.eq_univ_of_univ_subset fun x _ => ?_)
    by_contra hx
    exact h ⟨x, hx⟩
  have hdense : Dense ((ℐ.support.compl : Y.Opens) : Set Y) :=
    (ℐ.support.compl : Y.Opens).2.dense hUne
  have hrange : ((ℐ.support.compl : Y.Opens) : Set Y) ⊆ Set.range (blowUpToBase ℐ).base := by
    intro x hx
    have : IsIso (blowUpToBase ℐ ∣_ (ℐ.support.compl : Y.Opens)) :=
      isIso_blowUp_restrict_compl_support ℐ
    obtain ⟨z, hz⟩ := (asIso (blowUpToBase ℐ ∣_
      (ℐ.support.compl : Y.Opens))).hom.surjective (⟨x, hx⟩ : (ℐ.support.compl : Y.Opens))
    refine ⟨((blowUpToBase ℐ) ⁻¹ᵁ (ℐ.support.compl : Y.Opens)).ι z, ?_⟩
    have heq := congrArg (fun f => f z) (morphismRestrict_ι (blowUpToBase ℐ)
      (ℐ.support.compl : Y.Opens))
    change (blowUpToBase ℐ ∣_ (ℐ.support.compl : Y.Opens)) z = (⟨x, hx⟩ :
      (ℐ.support.compl : Y.Opens)) at hz
    simpa only [Scheme.Hom.comp_apply, hz, Scheme.Opens.ι_apply] using heq.symm
  have htop : Set.range (blowUpToBase ℐ).base = Set.univ := by
    refine Set.eq_univ_of_univ_subset ?_
    calc
      (Set.univ : Set Y) = closure ((ℐ.support.compl : Y.Opens) : Set Y) := hdense.closure_eq.symm
      _ ⊆ closure (Set.range (blowUpToBase ℐ).base) := closure_mono hrange
      _ = Set.range (blowUpToBase ℐ).base :=
        (blowUpToBase ℐ).isClosedMap.isClosed_range.closure_eq
  exact Set.range_eq_univ.mp htop

/-- A one-dimensional integral closed subscheme is not contained in a single point, so the
inverse image of a closed point has proper support on it. -/
private theorem comap_centerIdeal_support_ne_univ {X : Scheme.{u}} (I : X.IdealSheafData)
    [IsIntegral I.subscheme] (hdim : topologicalKrullDim I.subscheme = 1)
    (p : X) (hp : IsClosed ({p} : Set X)) :
    (((centerIdeal p hp).comap I.subschemeι).support : Set I.subscheme) ≠ Set.univ := by
  intro hall
  have hpoint : ∀ x : I.subscheme, I.subschemeι x = p := by
    intro x
    have hx : x ∈ (((centerIdeal p hp).comap I.subschemeι).support : Set I.subscheme) := by
      rw [hall]
      exact Set.mem_univ x
    rw [Scheme.IdealSheafData.support_comap] at hx
    change I.subschemeι x ∈ ((centerIdeal p hp).support : Set X) at hx
    rwa [show ((centerIdeal p hp).support : Set X) = {p} from
      Scheme.IdealSheafData.coe_support_vanishingIdeal _] at hx
  have : Subsingleton I.subscheme := ⟨fun x y =>
    I.subschemeι.isClosedEmbedding.injective ((hpoint x).trans (hpoint y).symm)⟩
  exact false_of_subsingleton_of_topologicalKrullDim_eq_one I.subscheme hdim

/-- **The strict transform of a one-dimensional integral closed subscheme covers it.** -/
private theorem surjective_transformToCurve {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) [IsIntegral I.subscheme]
    (hdim : topologicalKrullDim I.subscheme = 1) (p : X) (hp : IsClosed ({p} : Set X)) :
    Function.Surjective (transformToCurve I p hp).base := by
  have : IsNoetherian I.subscheme := isNoetherian_subscheme I
  have hsurj := surjective_blowUpToBase_of_support_ne_univ
    ((centerIdeal p hp).comap I.subschemeι) (comap_centerIdeal_support_ne_univ I hdim p hp)
  rw [← strictTransformBlowUpIso_hom_comp_blowUpToBase]
  exact hsurj.comp (Scheme.homeoOfIso ((Over.forget I.subscheme).mapIso
    (strictTransformBlowUpIso I.subschemeι (centerIdeal p hp)))).surjective

/-! ### Distinct curves have distinct strict transforms -/

/-- **One blowup at a closed point keeps two distinct one-dimensional integral closed
subschemes distinct**: the image of the support of each strict transform is the support of the
original. -/
private theorem transformIdeal_ne_of_ne {X : Scheme.{u}} [IsNoetherian X]
    (I J : X.IdealSheafData) [IsIntegral I.subscheme] [IsIntegral J.subscheme]
    (hdimI : topologicalKrullDim I.subscheme = 1)
    (hdimJ : topologicalKrullDim J.subscheme = 1) (hne : I ≠ J)
    (p : X) (hp : IsClosed ({p} : Set X)) :
    transformIdeal I p hp ≠ transformIdeal J p hp := by
  intro heq
  refine hne (eq_of_support_eq I J (SetLike.coe_injective ?_))
  rw [← image_transformIdeal_support_eq I p hp (surjective_transformToCurve I hdimI p hp), heq,
    image_transformIdeal_support_eq J p hp (surjective_transformToCurve J hdimJ p hp)]

/-! ### The number of intersection points -/

/-- Blowing up does not increase the number of intersection points of two curves, one of them
regular. -/
private theorem ncard_inter_transformIdeal_le {X : Scheme.{u}} [IsNoetherian X]
    (I J : X.IdealSheafData) [IsIntegral I.subscheme] [IsIntegral J.subscheme]
    (hdimI : topologicalKrullDim I.subscheme = 1)
    (hdimJ : topologicalKrullDim J.subscheme = 1) (hregI : IsRegular I.subscheme) (hne : I ≠ J)
    (p : X) (hp : IsClosed ({p} : Set X)) :
    (((transformIdeal I p hp).support : Set (blowUp (centerIdeal p hp))) ∩
      (transformIdeal J p hp).support).ncard ≤ ((I.support : Set X) ∩ J.support).ncard := by
  have hiso := transformToCurve_isIso_of_isRegular I hdimI hregI p hp
  have hinj : Function.Injective (transformToCurve I p hp).base :=
    (transformToCurve I p hp).homeomorph.injective
  exact Set.ncard_le_ncard_of_injOn _
    (fun q hq => ⟨transformIdeal_support_subset I p hp hq.1,
      transformIdeal_support_subset J p hp hq.2⟩)
    ((injOn_blowUpToBase_transformIdeal_support I p hp hinj).mono Set.inter_subset_left)
    (finite_inter_support I J hdimI hdimJ hne)

/-- Blowing up at an intersection point not reappearing on the exceptional divisor strictly
decreases the number of intersection points of two curves, one of them regular. -/
private theorem ncard_inter_transformIdeal_lt {X : Scheme.{u}} [IsNoetherian X]
    (I J : X.IdealSheafData) [IsIntegral I.subscheme] [IsIntegral J.subscheme]
    (hdimI : topologicalKrullDim I.subscheme = 1)
    (hdimJ : topologicalKrullDim J.subscheme = 1) (hregI : IsRegular I.subscheme) (hne : I ≠ J)
    (p : X) (hp : IsClosed ({p} : Set X)) (hpI : p ∈ I.support) (hpJ : p ∈ J.support)
    (hsep : ∀ q ∈ (((transformIdeal I p hp).support : Set (blowUp (centerIdeal p hp))) ∩
      (transformIdeal J p hp).support), blowUpToBase (centerIdeal p hp) q ≠ p) :
    (((transformIdeal I p hp).support : Set (blowUp (centerIdeal p hp))) ∩
      (transformIdeal J p hp).support).ncard < ((I.support : Set X) ∩ J.support).ncard := by
  have hiso := transformToCurve_isIso_of_isRegular I hdimI hregI p hp
  have hinj : Function.Injective (transformToCurve I p hp).base :=
    (transformToCurve I p hp).homeomorph.injective
  rw [← ((injOn_blowUpToBase_transformIdeal_support I p hp hinj).mono
    Set.inter_subset_left).ncard_image]
  refine Set.ncard_lt_ncard ?_ (finite_inter_support I J hdimI hdimJ hne)
  refine Set.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · rintro _ ⟨q, hq, rfl⟩
    exact ⟨transformIdeal_support_subset I p hp hq.1, transformIdeal_support_subset J p hp hq.2⟩
  · intro h
    obtain ⟨q, hq, hqp⟩ := h.symm ▸ (show p ∈ (I.support : Set X) ∩ J.support from ⟨hpI, hpJ⟩)
    exact hsep q hq hqp

/-! ### Properties transported along a chain -/


/-- A one-dimensional integral closed subscheme stays one-dimensional and integral along a chain
of blowups at closed points. -/
private theorem ChainTransform.integral_curve {X W : Scheme.{u}} [IsNoetherian X]
    {I : X.IdealSheafData} (hI : IsIntegral I.subscheme)
    (hdim : topologicalKrullDim I.subscheme = 1) {f : W ⟶ X} {K : W.IdealSheafData}
    (h : ChainTransform I f K) :
    IsIntegral K.subscheme ∧ topologicalKrullDim K.subscheme = 1 := by
  induction h with
  | refl => exact ⟨hI, hdim⟩
  | @step W' f' K' hK' w hw ih =>
      have : IsNoetherian W' := isNoetherian_of_pointBlowupChain hK'.pointBlowupChain
      have := ih.1
      exact transformIdeal_integral_curve K' ih.2 w hw

/-- A regular one-dimensional integral closed subscheme stays one along a chain of blowups at
closed points. -/
private theorem ChainTransform.regular_curve {X W : Scheme.{u}} [IsNoetherian X]
    {I : X.IdealSheafData} (hI : IsIntegral I.subscheme)
    (hdim : topologicalKrullDim I.subscheme = 1) (hreg : IsRegular I.subscheme) {f : W ⟶ X}
    {K : W.IdealSheafData} (h : ChainTransform I f K) :
    IsIntegral K.subscheme ∧ topologicalKrullDim K.subscheme = 1 ∧ IsRegular K.subscheme := by
  induction h with
  | refl => exact ⟨hI, hdim, hreg⟩
  | @step W' f' K' hK' w hw ih =>
      have : IsNoetherian W' := isNoetherian_of_pointBlowupChain hK'.pointBlowupChain
      have := ih.1
      exact transformIdeal_regular_curve K' ih.2.1 ih.2.2 w hw

/-- Disjoint closed subschemes stay disjoint along a chain of blowups at closed points. -/
private theorem FamilyTransform.disjoint {X W : Scheme.{u}} {n : ℕ}
    {Y : Fin n → X.IdealSheafData} {f : W ⟶ X} {J : Fin n → W.IdealSheafData}
    (h : FamilyTransform Y f J) {i j : Fin n}
    (hij : Disjoint (Y i).support (Y j).support) :
    Disjoint (J i).support (J j).support := by
  induction h with
  | refl => exact hij
  | step hJ w hw ih => exact disjoint_transformIdeal_support _ _ ih w hw

/-- **A family of pairwise distinct one-dimensional integral closed subschemes stays pairwise
distinct along a chain of blowups at closed points.** This is where the simultaneous relation is
needed: a chain does not determine the strict transform of a single member. -/
private theorem FamilyTransform.injective {X W : Scheme.{u}} [IsNoetherian X] {n : ℕ}
    {Y : Fin n → X.IdealSheafData} {f : W ⟶ X} {J : Fin n → W.IdealSheafData}
    (hI : ∀ i, IsIntegral (Y i).subscheme)
    (hdim : ∀ i, topologicalKrullDim (Y i).subscheme = 1) (hinj : Function.Injective Y)
    (h : FamilyTransform Y f J) : Function.Injective J := by
  induction h with
  | refl => exact hinj
  | @step W' f' J' hJ' w hw ih =>
      have hN : IsNoetherian W' := isNoetherian_of_pointBlowupChain hJ'.pointBlowupChain
      have hJi : ∀ i, IsIntegral (J' i).subscheme := fun i =>
        ((hJ'.chainTransform i).integral_curve (hI i) (hdim i)).1
      have hJd : ∀ i, topologicalKrullDim (J' i).subscheme = 1 := fun i =>
        ((hJ'.chainTransform i).integral_curve (hI i) (hdim i)).2
      intro a b hab
      by_contra hne
      have := hJi a
      have := hJi b
      exact transformIdeal_ne_of_ne (J' a) (J' b) (hJd a) (hJd b)
        (fun hJab => hne (ih hJab)) w hw hab

/-! ### Separating two regular curves -/

/-- Two members of a family can be separated if a finite chain of blowups of the ambient scheme
at closed points carries the family to one in which their supports are disjoint. -/
private abbrev CanSeparate {X : Scheme.{u}} {n : ℕ} (Y : Fin n → X.IdealSheafData)
    (i j : Fin n) : Prop :=
  ∃ (W : Scheme.{u}) (f : W ⟶ X) (J : Fin n → W.IdealSheafData),
    FamilyTransform Y f J ∧ Disjoint (J i).support (J j).support

/-- Already disjoint members are separated by the empty chain. -/
private theorem canSeparate_of_disjoint {X : Scheme.{u}} {n : ℕ} (Y : Fin n → X.IdealSheafData)
    (i j : Fin n) (h : Disjoint (Y i).support (Y j).support) : CanSeparate Y i j :=
  ⟨X, 𝟙 X, Y, .refl, h⟩

/-- Separating the simultaneous strict transforms separates the members. -/
private theorem canSeparate_of_step {X : Scheme.{u}} {n : ℕ} (Y : Fin n → X.IdealSheafData)
    (i j : Fin n) (p : X) (hp : IsClosed ({p} : Set X))
    (h : CanSeparate (fun k => transformIdeal (Y k) p hp) i j) : CanSeparate Y i j := by
  obtain ⟨W, f, J, hJ, hdisj⟩ := h
  exact ⟨W, f ≫ (blowUpToBase (centerIdeal p hp) ≫ 𝟙 X), J,
    (FamilyTransform.refl.step p hp).trans hJ, hdisj⟩

/-- **The intersection multiplicity of two curves at a closed point drops at a point of the
exceptional divisor**, by [Stacks, Tag 0BI7] part (3). -/
private theorem intersectionLength_transformIdeal_lt {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I J : X.IdealSheafData) [IsIntegral I.subscheme] [IsIntegral J.subscheme]
    (hdimI : topologicalKrullDim I.subscheme = 1)
    (hdimJ : topologicalKrullDim J.subscheme = 1) (hregI : IsRegular I.subscheme) (hne : I ≠ J)
    (p : X) (hp : p ∈ (I ⊔ J).support) (pc : IsClosed ({p} : Set X))
    (q : blowUp (centerIdeal p pc))
    (hqE : q ∈ (exceptionalIdeal (centerIdeal p pc)).support)
    (hq : q ∈ ((transformIdeal I p pc) ⊔ (transformIdeal J p pc)).support) :
    intersectionLength (transformIdeal I p pc) (transformIdeal J p pc) q hq <
      intersectionLength I J p hp := by
  have hpI : p ∈ I.support := (mem_support_sup_iff.mp hp).1
  have hstalk : IsLocallyNoetherian I.subscheme ∧
      ∀ z : I.subscheme, IsRegularLocalRing (I.subscheme.presheaf.stalk z) :=
    ((isRegular_tfae I.subscheme).out 1 2).mp hregI
  exact strictTransform_intersectionMultiplicity_lt
    (intersectionContext I J hdimI hdimJ hne p hp) ⟨p, hpI⟩ rfl (hstalk.2 _) q hqE hq

/-- Inner induction of `canSeparate_of_ncard_le`: given separation for fewer intersection
points, two regular curves meeting with multiplicity `m` at an intersection point can be
separated. -/
private theorem canSeparate_of_ncard_le_of_intersectionLength_eq (k : ℕ)
    (hk : ∀ k' < k, ∀ (X : Scheme.{u}), IsNoetherian X → ∀ (n : ℕ)
      (Y : Fin n → X.IdealSheafData) (i j : Fin n),
      IsIntegral (Y i).subscheme → IsIntegral (Y j).subscheme →
      topologicalKrullDim (Y i).subscheme = 1 → topologicalKrullDim (Y j).subscheme = 1 →
      IsRegular (Y i).subscheme → IsRegular (Y j).subscheme → Y i ≠ Y j →
      (((Y i).support : Set X) ∩ (Y j).support).ncard ≤ k' → CanSeparate Y i j)
    (m : ℕ) : ∀ (X : Scheme.{u}), IsNoetherian X → ∀ (n : ℕ)
      (Y : Fin n → X.IdealSheafData) (i j : Fin n),
      IsIntegral (Y i).subscheme → IsIntegral (Y j).subscheme →
      topologicalKrullDim (Y i).subscheme = 1 → topologicalKrullDim (Y j).subscheme = 1 →
      IsRegular (Y i).subscheme → IsRegular (Y j).subscheme → Y i ≠ Y j →
      (((Y i).support : Set X) ∩ (Y j).support).ncard ≤ k →
      ∀ (p : X) (hp : p ∈ (Y i ⊔ Y j).support),
        intersectionLength (Y i) (Y j) p hp = m → CanSeparate Y i j := by
  classical
  induction m using Nat.strong_induction_on with
  | h m hm =>
    intro X hX n Y i j hIi hIj hdi hdj hri hrj hne hc p hp heq
    have := hX
    have := hIi
    have := hIj
    have hpij := mem_support_sup_iff.mp hp
    have pc : IsClosed ({p} : Set X) :=
      isClosed_singleton_of_mem_inter_support (Y i) (Y j) hdi hdj hne p hpij.1 hpij.2
    obtain ⟨hIi', hdi', hri'⟩ := transformIdeal_regular_curve (Y i) hdi hri p pc
    obtain ⟨hIj', hdj', hrj'⟩ := transformIdeal_regular_curve (Y j) hdj hrj p pc
    have hne' := transformIdeal_ne_of_ne (Y i) (Y j) hdi hdj hne p pc
    refine canSeparate_of_step Y i j p pc ?_
    by_cases hex : ∃ q : blowUp (centerIdeal p pc),
        q ∈ ((transformIdeal (Y i) p pc) ⊔ (transformIdeal (Y j) p pc)).support ∧
          q ∈ (exceptionalIdeal (centerIdeal p pc)).support
    · obtain ⟨q, hq, hqE⟩ := hex
      have hlt := intersectionLength_transformIdeal_lt (Y i) (Y j) hdi hdj hri hne p hp pc
        q hqE hq
      rw [heq] at hlt
      exact hm _ hlt _ (isNoetherian_blowUp _) n (fun k => transformIdeal (Y k) p pc) i j
        hIi' hIj' hdi' hdj' hri' hrj' hne'
        ((ncard_inter_transformIdeal_le (Y i) (Y j) hdi hdj hri hne p pc).trans hc) q hq rfl
    · have hlt := ncard_inter_transformIdeal_lt (Y i) (Y j) hdi hdj hri hne p pc
        hpij.1 hpij.2 (by
          intro q hq hqp
          refine hex ⟨q, ?_, ?_⟩
          · exact mem_support_sup_iff.mpr hq
          · rw [mem_exceptionalIdeal_support_iff]
            exact hqp)
      exact hk _ (hlt.trans_le hc) _ (isNoetherian_blowUp _) n
        (fun k => transformIdeal (Y k) p pc) i j hIi' hIj' hdi' hdj' hri' hrj' hne' le_rfl

/-- **Two distinct regular curves with at most `k` intersection points can be separated.** The
induction is on the number of intersection points, and inside it on the multiplicity at one of
them: [Stacks, Tag 0BI7] part (3) lowers the multiplicity at a point of the exceptional divisor,
and when no intersection point of the strict transforms lies over the centre the number of
intersection points has dropped. -/
private theorem canSeparate_of_ncard_le (k : ℕ) :
    ∀ (X : Scheme.{u}), IsNoetherian X → ∀ (n : ℕ) (Y : Fin n → X.IdealSheafData) (i j : Fin n),
      IsIntegral (Y i).subscheme → IsIntegral (Y j).subscheme →
      topologicalKrullDim (Y i).subscheme = 1 → topologicalKrullDim (Y j).subscheme = 1 →
      IsRegular (Y i).subscheme → IsRegular (Y j).subscheme → Y i ≠ Y j →
      (((Y i).support : Set X) ∩ (Y j).support).ncard ≤ k → CanSeparate Y i j := by
  classical
  induction k using Nat.strong_induction_on with
  | h k hk =>
    intro X hX n Y i j hIi hIj hdi hdj hri hrj hne hc
    by_cases hd : Disjoint (Y i).support (Y j).support
    · exact canSeparate_of_disjoint Y i j hd
    · rw [disjoint_closeds_iff, Set.not_disjoint_iff] at hd
      obtain ⟨p, hpI, hpJ⟩ := hd
      exact canSeparate_of_ncard_le_of_intersectionLength_eq k hk _ X hX n Y i j hIi hIj hdi hdj
        hri hrj hne hc p (mem_support_sup_iff.mpr ⟨hpI, hpJ⟩) rfl

/-- **Two distinct regular curves can be separated.** -/
private theorem canSeparate_regular {X : Scheme.{u}} [IsNoetherian X] {n : ℕ}
    (Y : Fin n → X.IdealSheafData) (i j : Fin n)
    (hIi : IsIntegral (Y i).subscheme) (hIj : IsIntegral (Y j).subscheme)
    (hdi : topologicalKrullDim (Y i).subscheme = 1)
    (hdj : topologicalKrullDim (Y j).subscheme = 1)
    (hri : IsRegular (Y i).subscheme) (hrj : IsRegular (Y j).subscheme) (hne : Y i ≠ Y j) :
    CanSeparate Y i j :=
  canSeparate_of_ncard_le _ X inferInstance n Y i j hIi hIj hdi hdj hri hrj hne le_rfl

/-! ### Separating a finite family of regular curves -/

/-- **A finite set of pairs of a family of pairwise distinct regular curves can be made
disjoint**, one pair at a time. -/
private theorem exists_familyTransform_disjoint_on (n : ℕ) (S : Finset (Fin n × Fin n))
    (hS : ∀ a ∈ S, a.1 ≠ a.2) :
    ∀ (X : Scheme.{u}), IsNoetherian X → ∀ (Y : Fin n → X.IdealSheafData),
      Function.Injective Y → (∀ i, IsIntegral (Y i).subscheme) →
      (∀ i, topologicalKrullDim (Y i).subscheme = 1) → (∀ i, IsRegular (Y i).subscheme) →
      ∃ (W : Scheme.{u}) (f : W ⟶ X) (J : Fin n → W.IdealSheafData),
        FamilyTransform Y f J ∧ ∀ a ∈ S, Disjoint (J a.1).support (J a.2).support := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      intro X hX Y hinj hI hd hr
      exact ⟨X, 𝟙 X, Y, .refl, by simp⟩
  | @insert a S ha ih =>
      intro X hX Y hinj hI hd hr
      have := hX
      obtain ⟨W, f, J, hJ, hdisj⟩ := canSeparate_regular Y a.1 a.2 (hI a.1) (hI a.2)
        (hd a.1) (hd a.2) (hr a.1) (hr a.2) fun h => hS a (Finset.mem_insert_self _ _) (hinj h)
      have hWN : IsNoetherian W := isNoetherian_of_pointBlowupChain hJ.pointBlowupChain
      have hreg : ∀ i, IsIntegral (J i).subscheme ∧
          topologicalKrullDim (J i).subscheme = 1 ∧ IsRegular (J i).subscheme := fun i =>
        (hJ.chainTransform i).regular_curve (hI i) (hd i) (hr i)
      obtain ⟨V, g, K, hK, hKdisj⟩ := ih (fun b hb => hS b (Finset.mem_insert_of_mem hb))
        W hWN J (hJ.injective hI hd hinj) (fun i => (hreg i).1) (fun i => (hreg i).2.1)
        (fun i => (hreg i).2.2)
      refine ⟨V, g ≫ f, K, hJ.trans hK, fun b hb => ?_⟩
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact hK.disjoint hdisj
      · exact hKdisj b hb

/-! ### The resolution hypothesis is inherited by a blowup -/

/-- A modification of a one-dimensional integral Noetherian scheme is an alteration, and its
source is again one-dimensional: it is an isomorphism over a dense open by [Stacks, Tag 0BAJ],
hence finite and surjective, and a surjective integral morphism preserves dimension by
[Stacks, Tag 0ECG]. -/
private theorem isAlteration_and_dim_of_isModification {Y W : Scheme.{u}} [IsIntegral Y]
    [IsNoetherian Y] (hYdim : topologicalKrullDim Y = 1) {h : W ⟶ Y}
    (hW : IsIntegral W) (hP : IsProper h) (hB : IsBirational h) :
    IsAlteration h ∧ topologicalKrullDim W = 1 := by
  have : IsIntegral W := hW
  have : IsProper h := hP
  have : IsNoetherian W := isNoetherian_of_isProper_over_noetherian h
  have hdom : IsDominant h := ((tfae_isDominant_of_isIntegral h).out 1 2).mpr (by
    have := (IsBirational.bijOn hB).mapsTo
      (show genericPoint W ∈ genericPoints W by rw [genericPoints_eq_singleton]; rfl)
    rwa [genericPoints_eq_singleton, Set.mem_singleton_iff] at this)
  have : Finite (irreducibleComponents W) :=
    finite_irreducibleComponents_of_isNoetherian.to_subtype
  have : Finite (irreducibleComponents Y) :=
    finite_irreducibleComponents_of_isNoetherian.to_subtype
  obtain ⟨V, hVdense, hVi⟩ :=
    exists_dense_open_isIso_morphismRestrict_of_isBirational h hB (Or.inl inferInstance)
      (Or.inl ⟨inferInstance, inferInstance⟩)
  have : IsIso (h ∣_ V) := hVi
  have hVne : Nonempty V := by
    obtain ⟨v, hv⟩ := hVdense.nonempty
    exact ⟨⟨v, hv⟩⟩
  have halt : IsAlteration h := ⟨hP, hdom, hW, ⟨V, hVne, inferInstance⟩⟩
  refine ⟨halt, ?_⟩
  have : IsFinite h :=
    isFinite_of_isAlteration_of_topologicalKrullDim_le_one h halt (le_of_eq hYdim)
  have hrange : Set.range h.base = Set.univ :=
    h.isClosedMap.isClosed_range.closure_eq.symm.trans hdom.denseRange.closure_eq
  have : Surjective h := ⟨Set.range_eq_univ.mp hrange⟩
  rw [topologicalKrullDim_eq_of_isIntegralHom_of_surjective h, hYdim]

/-- A morphism restricting to an isomorphism over an open is injective on the inverse image of
that open. -/
private theorem injOn_of_isIso_morphismRestrict {A B : Scheme.{u}} (f : A ⟶ B) (U : B.Opens)
    (hU : IsIso (f ∣_ U)) : Set.InjOn f.base ((f ⁻¹ᵁ U : A.Opens) : Set A) := by
  have := hU
  intro z hz w hw hzw
  have hz' : (((f ∣_ U) (⟨z, hz⟩ : (f ⁻¹ᵁ U).toScheme)).1 : B) = f z :=
    morphismRestrict_base_coe f U _
  have hw' : (((f ∣_ U) (⟨w, hw⟩ : (f ⁻¹ᵁ U).toScheme)).1 : B) = f w :=
    morphismRestrict_base_coe f U _
  have heq : (f ∣_ U) (⟨z, hz⟩ : (f ⁻¹ᵁ U).toScheme) = (f ∣_ U) (⟨w, hw⟩ : (f ⁻¹ᵁ U).toScheme) :=
    Subtype.ext (hz'.trans (hzw.trans hw'.symm))
  exact congrArg (fun t : (f ⁻¹ᵁ U).toScheme => t.1) ((f ∣_ U).homeomorph.injective heq)

/-- A proper morphism `l` to an irreducible scheme is surjective when its composite with a
dominant morphism `b`, an isomorphism over a nonempty open, is surjective. -/
private theorem surjective_of_comp_eq_of_isIso_morphismRestrict {Z B Y : Scheme.{u}}
    [IrreducibleSpace B] {l : Z ⟶ B} [IsProper l] {b : B ⟶ Y} (hb : IsDominant b)
    {g : Z ⟶ Y} [Surjective g] (hl : l ≫ b = g) (V : Y.Opens) (hV : (V : Set Y).Nonempty)
    (hVi : IsIso (b ∣_ V)) : Surjective l := by
  have hVsub : ((b ⁻¹ᵁ V : B.Opens) : Set B) ⊆ Set.range l.base := by
    intro w hw
    obtain ⟨z, hz⟩ := g.surjective (b w)
    refine ⟨z, ?_⟩
    have hbz : b (l z) = b w := by
      have hzz := congrArg (fun k => k z) hl
      simp only [Scheme.Hom.comp_apply] at hzz
      rw [hzz]
      exact hz
    have hlz : l z ∈ ((b ⁻¹ᵁ V : B.Opens) : Set B) := by
      change b (l z) ∈ (V : Set Y)
      rw [hbz]
      exact hw
    exact injOn_of_isIso_morphismRestrict b V hVi hlz hw hbz
  have hVne : ((b ⁻¹ᵁ V : B.Opens) : Set B).Nonempty := by
    obtain ⟨x, hxV, w, hw⟩ := hb.denseRange.inter_open_nonempty (V : Set Y) V.2 hV
    refine ⟨w, ?_⟩
    change b w ∈ (V : Set Y)
    rw [hw]
    exact hxV
  refine ⟨Set.range_eq_univ.mp (Set.eq_univ_of_univ_subset ?_)⟩
  calc
    (Set.univ : Set B) = closure ((b ⁻¹ᵁ V : B.Opens) : Set B) :=
      ((b ⁻¹ᵁ V : B.Opens).2.dense hVne).closure_eq.symm
    _ ⊆ closure (Set.range l.base) := closure_mono hVsub
    _ = Set.range l.base := l.isClosedMap.isClosed_range.closure_eq

/-- **The equivalent conditions of [Stacks, Tag 0BI4] pass to the blowup in an ideal sheaf with
proper support.** A resolution of singularities of the base is regular of dimension one, hence
factors through the blowup by its universal property, and the factorisation is again proper,
surjective and birational. -/
private theorem exists_modification_isRegular_blowUp {Y : Scheme.{u}} [IsIntegral Y]
    [IsNoetherian Y] (hYdim : topologicalKrullDim Y = 1) (ℐ : Y.IdealSheafData)
    (hproper : (ℐ.support : Set Y) ≠ Set.univ)
    (hY : ∃ (Z : Scheme.{u}) (g : Z ⟶ Y), IsAlteration g ∧ IsRegular Z) :
    ∃ (Z : Scheme.{u}) (g : Z ⟶ blowUp ℐ),
      IsIntegral Z ∧ IsProper g ∧ IsBirational g ∧ IsRegular Z := by
  have : IrreducibleSpace Y := irreducibleSpace_of_isIntegral Y
  have hℐ : ℐ ≠ ⊥ := by
    intro h
    refine hproper ?_
    rw [h, Scheme.IdealSheafData.support_bot]
    rfl
  have : IsIntegral (blowUp ℐ) := isIntegral_blowUp ℐ hℐ
  have : IsNoetherian (blowUp ℐ) := isNoetherian_blowUp ℐ
  have : IrreducibleSpace (blowUp ℐ) := irreducibleSpace_of_isIntegral (blowUp ℐ)
  have hbbir : IsBirational (blowUpToBase ℐ) := isBirational_blowUpToBase ℐ hℐ
  obtain ⟨hbalt, hBldim⟩ :=
    isAlteration_and_dim_of_isModification hYdim ‹IsIntegral (blowUp ℐ)› inferInstance hbbir
  obtain ⟨Z, g, ⟨hgbir, hgprop, hgint⟩, hreg⟩ := ((resolveCurve_tfae Y hYdim).out 1 2).mp hY
  have : IsIntegral Z := hgint
  have : IsProper g := hgprop
  have : IsNoetherian Z := isNoetherian_of_isProper_over_noetherian g
  have : IrreducibleSpace Z := irreducibleSpace_of_isIntegral Z
  obtain ⟨hgalt, hZdim⟩ := isAlteration_and_dim_of_isModification hYdim hgint hgprop hgbir
  have : IsDominant g := hgalt.2.1
  have : Surjective g :=
    surjective_of_isDominant_of_isClosed_range g g.isClosedMap.isClosed_range
  obtain ⟨l, hl⟩ := exists_lift_blowUpToBase_of_isRegular (le_of_eq hZdim) hreg ℐ g hproper
  have : IsProper l := by
    have : IsProper (l ≫ blowUpToBase ℐ) := hl ▸ hgprop
    exact IsProper.of_comp l (blowUpToBase ℐ)
  have : Finite (irreducibleComponents (blowUp ℐ)) :=
    finite_irreducibleComponents_of_isNoetherian.to_subtype
  have : Finite (irreducibleComponents Y) :=
    finite_irreducibleComponents_of_isNoetherian.to_subtype
  obtain ⟨V, hVdense, hVi⟩ :=
    exists_dense_open_isIso_morphismRestrict_of_isBirational (blowUpToBase ℐ) hbbir
      (Or.inl inferInstance) (Or.inl ⟨inferInstance, inferInstance⟩)
  have : Surjective l := surjective_of_comp_eq_of_isIso_morphismRestrict hbalt.2.1 hl V
    hVdense.nonempty hVi
  have hlη : l (genericPoint Z) = genericPoint (blowUp ℐ) := genericPoint_eq_of_surjective l
  have : IsIso ((blowUpToBase ℐ).stalkMap (l (genericPoint Z))) := by
    rw [hlη]
    exact IsBirational.isIso_stalkMap hbbir _ (by rw [genericPoints_eq_singleton]; rfl)
  have hcomp : IsIso ((l ≫ blowUpToBase ℐ).stalkMap (genericPoint Z)) := by
    rw [hl]
    exact IsBirational.isIso_stalkMap hgbir _ (by rw [genericPoints_eq_singleton]; rfl)
  rw [Scheme.Hom.stalkMap_comp] at hcomp
  have : IsIso (l.stalkMap (genericPoint Z)) :=
    (isIso_comp_left_iff ((blowUpToBase ℐ).stalkMap (l (genericPoint Z)))
      (l.stalkMap (genericPoint Z))).mp hcomp
  exact ⟨Z, l, hgint, inferInstance, isBirational_of_isIso_stalkMap_genericPoint l, hreg⟩

/-- **The equivalent conditions of [Stacks, Tag 0BI4] are inherited by the strict transform of a
one-dimensional integral closed subscheme under one blowup at a closed point.** The strict
transform is the blowup of the subscheme in the inverse image of the centre, by
[Stacks, Tag 080E]. -/
private theorem exists_pointBlowupChain_isRegular_transformIdeal {X : Scheme.{u}}
    [IsNoetherian X] (I : X.IdealSheafData) (hI : IsIntegral I.subscheme)
    (hdim : topologicalKrullDim I.subscheme = 1)
    (hres : ∃ (V : Scheme.{u}) (g : V ⟶ I.subscheme),
      PointBlowupChain I.subscheme Set.univ V g ∧ IsRegular V)
    (p : X) (hp : IsClosed ({p} : Set X)) :
    ∃ (V : Scheme.{u}) (g : V ⟶ (transformIdeal I p hp).subscheme),
      PointBlowupChain (transformIdeal I p hp).subscheme Set.univ V g ∧ IsRegular V := by
  have := hI
  have : IsNoetherian I.subscheme := isNoetherian_subscheme I
  have hres1 : ∃ (Z : Scheme.{u}) (g : Z ⟶ I.subscheme), IsAlteration g ∧ IsRegular Z :=
    ((resolveCurve_tfae I.subscheme hdim).out 3 1).mp hres
  obtain ⟨Z, l, hZint, hlprop, hlbir, hreg⟩ := exists_modification_isRegular_blowUp hdim
    ((centerIdeal p hp).comap I.subschemeι) (comap_centerIdeal_support_ne_univ I hdim p hp)
    hres1
  obtain ⟨e₁⟩ := nonempty_transformIdeal_subscheme_iso_transform I p hp
  have e : (transformIdeal I p hp).subscheme ≅
      blowUp ((centerIdeal p hp).comap I.subschemeι) :=
    e₁ ≪≫ (Over.forget I.subscheme).mapIso
      (strictTransformBlowUpIso I.subschemeι (centerIdeal p hp))
  obtain ⟨hTint, hTdim⟩ := transformIdeal_integral_curve I hdim p hp
  have : IsIntegral (transformIdeal I p hp).subscheme := hTint
  have : IsNoetherian (blowUp (centerIdeal p hp)) := isNoetherian_blowUp _
  have : IsNoetherian (transformIdeal I p hp).subscheme :=
    isNoetherian_subscheme (transformIdeal I p hp)
  have : IsIntegral Z := hZint
  have : IsIntegral (blowUp ((centerIdeal p hp).comap I.subschemeι)) :=
    IsIntegral.of_isIso e.hom
  have : IsProper l := hlprop
  have hcond : ∃ (Z' : Scheme.{u}) (g : Z' ⟶ (transformIdeal I p hp).subscheme),
      IsAlteration g ∧ IsRegular Z' :=
    ⟨Z, l ≫ e.inv, (isAlteration_and_dim_of_isModification hTdim hZint inferInstance
      (IsBirational.comp hlbir (isBirational_of_isIso e.inv))).1, hreg⟩
  exact ((resolveCurve_tfae (transformIdeal I p hp).subscheme hTdim).out 1 3).mp hcond

/-- The equivalent conditions of [Stacks, Tag 0BI4] are inherited along a chain of blowups at
closed points. -/
private theorem ChainTransform.exists_pointBlowupChain_isRegular {X W : Scheme.{u}}
    [IsNoetherian X] {I : X.IdealSheafData} {f : W ⟶ X} {K : W.IdealSheafData}
    (h : ChainTransform I f K) (hI : IsIntegral I.subscheme)
    (hdim : topologicalKrullDim I.subscheme = 1)
    (hres : ∃ (V : Scheme.{u}) (g : V ⟶ I.subscheme),
      PointBlowupChain I.subscheme Set.univ V g ∧ IsRegular V) :
    ∃ (V : Scheme.{u}) (g : V ⟶ K.subscheme),
      PointBlowupChain K.subscheme Set.univ V g ∧ IsRegular V := by
  induction h with
  | refl => exact hres
  | @step W' f' K' hK' w hw ih =>
      have : IsNoetherian W' := isNoetherian_of_pointBlowupChain hK'.pointBlowupChain
      obtain ⟨hK'I, hK'd⟩ := hK'.integral_curve hI hdim
      exact exists_pointBlowupChain_isRegular_transformIdeal K' hK'I hK'd ih w hw

/-! ### Resolving a finite family of curves -/

/-- **A finite set of indices of a family of one-dimensional integral closed subschemes each
satisfying the equivalent conditions of [Stacks, Tag 0BI4] can be made regular**, one index at
a time, the other members of the family being carried along. -/
private theorem exists_familyTransform_isRegular_on (n : ℕ) (S : Finset (Fin n)) :
    ∀ (X : Scheme.{u}), IsNoetherian X → ∀ (Y : Fin n → X.IdealSheafData),
      (∀ i, IsIntegral (Y i).subscheme) → (∀ i, topologicalKrullDim (Y i).subscheme = 1) →
      (∀ i, ∃ (V : Scheme.{u}) (g : V ⟶ (Y i).subscheme),
        PointBlowupChain (Y i).subscheme Set.univ V g ∧ IsRegular V) →
      ∃ (W : Scheme.{u}) (f : W ⟶ X) (J : Fin n → W.IdealSheafData),
        FamilyTransform Y f J ∧ ∀ i ∈ S, IsRegular (J i).subscheme := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      intro X hX Y hI hd hr
      exact ⟨X, 𝟙 X, Y, .refl, by simp⟩
  | @insert a S ha ih =>
      intro X hX Y hI hd hr
      have := hX
      obtain ⟨W, f, J, hJ, -, -, hJar⟩ :=
        exists_familyTransform_isRegular_of_pointBlowupChain Y a (hI a) (hd a) (hr a)
      have hWN : IsNoetherian W := isNoetherian_of_pointBlowupChain hJ.pointBlowupChain
      have hJint : ∀ i, IsIntegral (J i).subscheme ∧ topologicalKrullDim (J i).subscheme = 1 :=
        fun i => (hJ.chainTransform i).integral_curve (hI i) (hd i)
      obtain ⟨V, g, K, hK, hKr⟩ := ih W hWN J (fun i => (hJint i).1) (fun i => (hJint i).2)
        fun i => (hJ.chainTransform i).exists_pointBlowupChain_isRegular (hI i) (hd i) (hr i)
      refine ⟨V, g ≫ f, K, hJ.trans hK, fun i hi => ?_⟩
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact ((hK.chainTransform i).regular_curve (hJint i).1 (hJint i).2 hJar).2.2
      · exact hKr i hi

/-- **Stacks Project, Tag 0BI8.** Let `X` be a Noetherian scheme and let
`Y : Fin n → X.IdealSheafData` be pairwise distinct integral closed subschemes of dimension one,
each admitting a finite chain of blowups in closed points with regular source — one of the
equivalent conditions of [Stacks, Tag 0BI4]. Then there is a finite chain of blowups of `X` at
closed points along which the strict transforms of the `Y i` become pairwise disjoint regular
curves. -/
@[stacks 0BI8]
public theorem exists_pointBlowupChain_familyTransform_isRegular_pairwise_disjoint
    {X : Scheme.{u}} [IsNoetherian X] {n : ℕ} (Y : Fin n → X.IdealSheafData)
    (hYne : Function.Injective Y) (hYint : ∀ i, IsIntegral (Y i).subscheme)
    (hYdim : ∀ i, topologicalKrullDim (Y i).subscheme = 1)
    (hYres : ∀ i, ∃ (V : Scheme.{u}) (g : V ⟶ (Y i).subscheme),
      PointBlowupChain (Y i).subscheme Set.univ V g ∧ IsRegular V) :
    ∃ (W : Scheme.{u}) (f : W ⟶ X) (J : Fin n → W.IdealSheafData),
      PointBlowupChain X Set.univ W f ∧ FamilyTransform Y f J ∧
        (∀ i, IsIntegral (J i).subscheme ∧ topologicalKrullDim (J i).subscheme = 1 ∧
          IsRegular (J i).subscheme) ∧
        Pairwise fun i j : Fin n => Disjoint (J i).support (J j).support := by
  classical
  obtain ⟨W, f, J, hJ, hJreg⟩ :=
    exists_familyTransform_isRegular_on n Finset.univ X inferInstance Y hYint hYdim hYres
  have hWN : IsNoetherian W := isNoetherian_of_pointBlowupChain hJ.pointBlowupChain
  have hJint : ∀ i, IsIntegral (J i).subscheme ∧ topologicalKrullDim (J i).subscheme = 1 :=
    fun i => (hJ.chainTransform i).integral_curve (hYint i) (hYdim i)
  have hJr : ∀ i, IsRegular (J i).subscheme := fun i => hJreg i (Finset.mem_univ i)
  obtain ⟨V, g, K, hK, hKdisj⟩ := exists_familyTransform_disjoint_on n
    (Finset.univ.filter fun a : Fin n × Fin n => a.1 ≠ a.2)
    (fun a ha => (Finset.mem_filter.mp ha).2) W hWN J (hJ.injective hYint hYdim hYne)
    (fun i => (hJint i).1) (fun i => (hJint i).2) hJr
  refine ⟨V, g ≫ f, K, (hJ.trans hK).pointBlowupChain, hJ.trans hK, fun i => ?_,
    fun i j hij => hKdisj (i, j) (by simp [hij])⟩
  exact (hK.chainTransform i).regular_curve (hJint i).1 (hJint i).2 (hJr i)

end AlgebraicGeometry

end
