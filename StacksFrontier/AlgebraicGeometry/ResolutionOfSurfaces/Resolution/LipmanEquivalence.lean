module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.TorsionFree
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedPointSupport.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Dominant
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.IsoOverDenseOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Stability
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.Alteration
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.IntegralSchemes
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleBasics.FlatLocusOpenness
public import StacksFrontier.AlgebraicGeometry.Morphisms.Integral.Dimension
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.UniversalProperty
public import StacksFrontier.AlgebraicGeometry.NormalizationBirational.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.AlgebraicGeometry.Properties.RegularCharacterization
public import StacksFrontier.AlgebraicGeometry.Pullback.StalkFromSpecStalk
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ImpliedProperties.FiniteNormalization
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ImpliedProperties.LocalDomain
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.NormalizedBlowUpReduction
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.NormalizedBlowUps
public import StacksFrontier.RingTheory.AdicCompletion.Normal
public import StacksFrontier.RingTheory.RegularLocalRing.FlatLocalHom

/-!
# Resolution of a two-dimensional integral Noetherian scheme

For a two-dimensional integral Noetherian scheme `Y` the following four conditions are
equivalent:

1. there is an alteration `X ⟶ Y` with `X` regular;
2. there is a resolution of singularities of `Y`;
3. `Y` has a resolution of singularities by normalized blowups;
4. the normalization `Y^ν ⟶ Y` is finite, `Y^ν` has finitely many singular points, and the
   local ring of `Y^ν` at each of them has normal completion.

This file proves the three implications `(3) ⇒ (2)`, `(2) ⇒ (1)` and `(1) ⇒ (4)`, which travel
once down the chain of conditions; every implication from an earlier to a later condition is a
composite of these. What is missing for the equivalence is a single implication out of condition
`(4)`, which is where the construction of a resolution lives: one produces a resolution by
normalized blowups of the spectrum of each completed local ring and descends and globalizes it.

## Main results

* `AlgebraicGeometry.isModification_of_normalizedBlowUpChain`: the structure morphism of a
  sequence consisting of the normalization of `Y` followed by normalized blowups at closed
  points is a modification. This is what makes a resolution by normalized blowups a resolution.
* `AlgebraicGeometry.exists_resolution_of_hasResolutionByNormalizedBlowUps` is the implication
  `(3) ⇒ (2)`.
* `AlgebraicGeometry.isAlteration_of_isResolution`: a resolution of singularities is an
  alteration, since a proper birational morphism is an isomorphism over a dense open of its
  target and so in particular finite there.
* `AlgebraicGeometry.exists_regular_alteration_of_exists_resolution` is the implication
  `(2) ⇒ (1)`.
* `AlgebraicGeometry.finite_normalization_and_normal_completions_of_exists_regular_alteration`
  is the implication `(1) ⇒ (4)`.

## Implementation notes

The four conditions are spelled with the library's own predicates: an alteration is
`AlgebraicGeometry.IsAlteration`, a resolution of singularities is
`AlgebraicGeometry.IsResolution`, regularity is `AlgebraicGeometry.IsRegular`, and a resolution
by normalized blowups is `AlgebraicGeometry.HasResolutionByNormalizedBlowUps`, whose underlying
sequence is the inductive predicate `AlgebraicGeometry.NormalizedBlowUpChain`. That predicate
carries properness of the morphism down to `Y` at every stage, so properness of the composite
needs no induction; what the induction supplies is birationality and integrality.

Birationality of a normalized blowup requires a point other than its centre, which is where
two-dimensionality of `Y` is used: a proper birational morphism onto an integral scheme is
surjective, so every stage of the sequence has at least as many points as `Y`, and a scheme of
dimension two is not a one-point space.

The implication `(2) ⇒ (1)` needs neither the dimension of `Y` nor, beyond local
Noetherianness, its quasi-compactness; it is stated for an integral Noetherian scheme, as the
condition `(2)` only makes sense there.

For the implication `(1) ⇒ (4)` the finiteness hypothesis on irreducible components of
quasi-compact opens, under which the normalization is defined, is carried as an explicit
argument, as everywhere in the normalization API; it is a proposition and holds on a Noetherian
scheme, so the morphism it names is unambiguous. The alteration is transported to the
normalization by its universal property, the source of an alteration by a regular scheme being
normal. The two assertions about the normalization are then local statements about a normal
integral Noetherian scheme of dimension at most two carrying an alteration by a regular scheme:
the singular locus is contained in the image of the locus where the alteration fails to be flat,
because regularity descends along a flat local homomorphism, and that image is closed and
consists of closed points; and the completion of a local ring is handled by base changing the
alteration along the morphism out of the spectrum of that local ring, which is a flat
preimmersion, and feeding the result to [Stacks, Tag 0BGI], whose conclusion about the integral
closure is brought back to the local ring itself by [Stacks, Tag 0BGH].

## References

* [Lipman, *Rational singularities*, Theorem on page 151]
* [Stacks Project, Tag 0BGP](https://stacks.math.columbia.edu/tag/0BGP)
* [Stacks Project, Tag 0BGG](https://stacks.math.columbia.edu/tag/0BGG)
* [Stacks Project, Tag 0BGH](https://stacks.math.columbia.edu/tag/0BGH)
* [Stacks Project, Tag 0BGI](https://stacks.math.columbia.edu/tag/0BGI)
* [Stacks Project, Tag 0BGK](https://stacks.math.columbia.edu/tag/0BGK)
* [Stacks Project, Tag 0BGL](https://stacks.math.columbia.edu/tag/0BGL)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### A resolution by normalized blowups is a resolution -/

/-- The structure morphism of a sequence consisting of the normalization of a two-dimensional
integral Noetherian scheme `Y` followed by finitely many normalized blowups at closed points is
a modification of `Y`.

Properness is the properness carried by the sequence itself. Birationality and integrality are
inductive: the normalization of a reduced scheme is birational and the normalization of an
integral scheme is integral, while a normalized blowup at a closed point `x` of an integral
scheme is birational and has integral source as soon as some point differs from `x`. Such a
point exists because each stage maps onto `Y`, a proper birational morphism onto an integral
scheme being surjective, and because a two-dimensional scheme has more than one point. -/
theorem isModification_of_normalizedBlowUpChain {Y : Scheme.{u}} [IsIntegral Y]
    (hdim : topologicalKrullDim Y = 2)
    {hY : ∀ U : Y.Opens, IsCompact (U : Set Y) → (irreducibleComponents U).Finite}
    {X : Scheme.{u}} {f : X ⟶ Y} (hchain : NormalizedBlowUpChain Y hY X f) :
    IsModification f := by
  induction hchain with
  | normalization hproper =>
      exact ⟨Scheme.isBirational_normalization Y hY, hproper, inferInstance⟩
  | @blowUp W g _ hX x hx hproper ih =>
      have : IsProper g := ih.isProper
      have : IsIntegral W := ih.source_isIntegral
      obtain ⟨z, hz⟩ := exists_ne_of_topologicalKrullDim_eq_two hdim (g x)
      obtain ⟨w, hw⟩ := surjective_of_isProper_of_isBirational g ih.isBirational z
      have hwx : w ≠ x := by
        rintro rfl
        exact hz hw.symm
      exact ⟨(isBirational_normalizedBlowUp hX x hx hwx).comp ih.isBirational, hproper,
        isIntegral_normalizedBlowUpScheme hX x hx hwx⟩

/-- **A resolution of singularities by normalized blowups is a resolution of singularities.**
This is the implication `(3) ⇒ (2)` of the theorem on resolution of two-dimensional schemes
([Stacks, Tag 0BGP], registered in full on `AlgebraicGeometry.tfae_exists_isAlteration_isRegular`).
-/
theorem exists_resolution_of_hasResolutionByNormalizedBlowUps (Y : Scheme.{u}) [IsIntegral Y]
    [IsNoetherian Y] (hdim : topologicalKrullDim Y = 2)
    (hres : HasResolutionByNormalizedBlowUps Y) :
    ∃ (X : Scheme.{u}) (f : X ⟶ Y), IsResolution f := by
  obtain ⟨_, X, f, hchain, hreg⟩ := hres
  exact ⟨X, f, isModification_of_normalizedBlowUpChain hdim hchain, hreg⟩

/-! ### A resolution is an alteration by a regular scheme -/

/-- The generic point of an integral scheme lies in every nonempty open subset. -/
private theorem genericPoint_mem_of_nonempty {Y : Scheme.{u}} [IsIntegral Y] (U : Y.Opens)
    (hU : Nonempty U) : genericPoint Y ∈ U := by
  obtain ⟨y⟩ := hU
  exact (genericPoint_specializes y.1).mem_open U.isOpen y.2

/-- A separated birational morphism locally of finite type between integral schemes is an
isomorphism over a nonempty open subset of its target. -/
private theorem exists_nonempty_open_isIso_morphismRestrict {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] (hf : IsBirational f) :
    ∃ V : Y.Opens, Nonempty V ∧ IsIso (f ∣_ V) := by
  have : Finite (irreducibleComponents X) := by
    rw [irreducibleComponents_eq_singleton]
    infer_instance
  have : Finite (irreducibleComponents Y) := by
    rw [irreducibleComponents_eq_singleton]
    infer_instance
  obtain ⟨V, hVdense, hViso⟩ := exists_dense_open_isIso_morphismRestrict_of_isBirational f hf
    (Or.inr inferInstance) (Or.inl ⟨inferInstance, inferInstance⟩)
  obtain ⟨y, hy⟩ := hVdense.nonempty
  exact ⟨V, ⟨⟨y, hy⟩⟩, hViso⟩

/-- **A resolution of singularities is an alteration.** A resolution is proper with integral
source, and birational, hence dominant; and a birational morphism between schemes with finitely
many irreducible components is an isomorphism over a dense open subscheme of its target, so in
particular finite there. -/
theorem isAlteration_of_isResolution {X Y : Scheme.{u}} [IsIntegral Y] [IsNoetherian Y]
    {f : X ⟶ Y} (hf : IsResolution f) : IsAlteration f := by
  have : IsProper f := hf.isModification.isProper
  have : IsIntegral X := hf.isModification.source_isIntegral
  obtain ⟨V, hV, _⟩ :=
    exists_nonempty_open_isIso_morphismRestrict f hf.isModification.isBirational
  exact ⟨inferInstance, hf.isModification.isBirational.isDominant, inferInstance, V, hV,
    inferInstance⟩

/-- **A scheme with a resolution of singularities has an alteration by a regular scheme.** This
is the implication `(2) ⇒ (1)` of the theorem on resolution of two-dimensional schemes; it holds
in any dimension. -/
theorem exists_regular_alteration_of_exists_resolution (Y : Scheme.{u}) [IsIntegral Y]
    [IsNoetherian Y] (hres : ∃ (X : Scheme.{u}) (f : X ⟶ Y), IsResolution f) :
    ∃ (X : Scheme.{u}) (f : X ⟶ Y), IsAlteration f ∧ IsRegular X := by
  obtain ⟨X, f, hf⟩ := hres
  exact ⟨X, f, isAlteration_of_isResolution hf, hf.source_isRegular⟩

/-! ### A regular alteration lifts to the normalization -/

/-- A morphism to an integral scheme is dominant as soon as its composite with a second morphism
is surjective and that second morphism is an isomorphism over an open subset of its own target
containing the image of the generic point: some point then maps to the generic point. -/
private theorem isDominant_of_surjective_comp_of_isIso_morphismRestrict
    {X N Y : Scheme.{u}} [IsIntegral N] (g : X ⟶ N) (ν : N ⟶ Y) [Surjective (g ≫ ν)]
    (V : Y.Opens) [IsIso (ν ∣_ V)] (hη : ν (genericPoint N) ∈ V) : IsDominant g := by
  obtain ⟨x, hx⟩ := (g ≫ ν).surjective (ν (genericPoint N))
  change ν (g x) = ν (genericPoint N) at hx
  have hxV : ν (g x) ∈ V := by rwa [hx]
  have hrestrict (t : (ν ⁻¹ᵁ V).toScheme) : V.ι ((ν ∣_ V) t) = ν ((ν ⁻¹ᵁ V).ι t) :=
    congrArg (fun h : (ν ⁻¹ᵁ V).toScheme ⟶ Y => h t) (morphismRestrict_ι ν V)
  have h₁ : V.ι ((ν ∣_ V) (⟨g x, hxV⟩ : (ν ⁻¹ᵁ V).toScheme)) = ν (g x) :=
    hrestrict ⟨g x, hxV⟩
  have h₂ : V.ι ((ν ∣_ V) (⟨genericPoint N, hη⟩ : (ν ⁻¹ᵁ V).toScheme)) =
      ν (genericPoint N) := hrestrict ⟨genericPoint N, hη⟩
  have hab : (ν ∣_ V) (⟨g x, hxV⟩ : (ν ⁻¹ᵁ V).toScheme) =
      (ν ∣_ V) (⟨genericPoint N, hη⟩ : (ν ⁻¹ᵁ V).toScheme) :=
    Subtype.ext (h₁.trans (hx.trans h₂.symm))
  have hpoint : g x = genericPoint N := congrArg Subtype.val ((ν ∣_ V).injective hab)
  refine ⟨?_⟩
  rw [denseRange_iff_closure_range]
  refine Set.Subset.antisymm (Set.subset_univ _) ?_
  rw [← genericPoint_closure N]
  exact closure_mono (Set.singleton_subset_iff.mpr ⟨x, hpoint⟩)

/-- **An alteration by a regular scheme lifts to an alteration of the normalization.** The
source of the alteration is regular, hence normal, so the alteration factors uniquely through
the normalization; the lift is proper because the normalization is separated, dominant because
the normalization is an isomorphism over a dense open of the target, and finite over the
preimage of an open over which the original alteration is finite. -/
private theorem exists_isAlteration_lift_normalization (Y : Scheme.{u}) [IsIntegral Y]
    [IsNoetherian Y]
    (hY : ∀ U : Y.Opens, IsCompact (U : Set Y) → (irreducibleComponents U).Finite)
    (X : Scheme.{u}) (f : X ⟶ Y) (hf : IsAlteration f) (hreg : IsRegular X)
    (hfin : IsFinite (Scheme.normalization Y hY)) :
    ∃ g : X ⟶ Y.normalizationScheme hY,
      g ≫ Scheme.normalization Y hY = f ∧ IsAlteration g := by
  let ν := Scheme.normalization Y hY
  have : IsFinite ν := hfin
  have : IsProper f := hf.1
  have : IsDominant f := hf.2.1
  have : IsIntegral X := hf.2.2.1
  have : IsNormal X := isNormal_of_isRegular X hreg
  have hgen : f (genericPoint X) = genericPoint Y :=
    ((tfae_isDominant_of_isIntegral f).out 1 2).mp hf.2.1
  have hgeneric : ∀ η : genericPoints X, f η.1 ∈ genericPoints Y := by
    intro η
    have hη : η.1 = genericPoint X := by
      simpa [genericPoints_eq_singleton] using η.2
    rw [hη, hgen, genericPoints_eq_singleton]
    exact Set.mem_singleton _
  obtain ⟨g, hg, -⟩ := Scheme.existsUnique_lift_normalization hY f hgeneric
  have hgν : g ≫ ν = f := hg
  have : IsProper (g ≫ ν) := by
    rw [hgν]
    infer_instance
  have : IsProper g := IsProper.of_comp g ν
  have : Surjective (g ≫ ν) := by
    rw [hgν]
    exact Surjective.of_universallyClosed_of_isDominant f
  have hνbir : IsBirational ν := Scheme.isBirational_normalization Y hY
  obtain ⟨V, hV, _⟩ := exists_nonempty_open_isIso_morphismRestrict ν hνbir
  have hνgen : ν (genericPoint (Y.normalizationScheme hY)) = genericPoint Y :=
    ((tfae_isDominant_of_isIntegral ν).out 1 2).mp hνbir.isDominant
  have hηV : ν (genericPoint (Y.normalizationScheme hY)) ∈ V := by
    rw [hνgen]
    exact genericPoint_mem_of_nonempty V hV
  have hdom : IsDominant g :=
    isDominant_of_surjective_comp_of_isIso_morphismRestrict g ν V hηV
  obtain ⟨U, hUne, hUfin⟩ := hf.2.2.2
  have hηU : genericPoint Y ∈ U := genericPoint_mem_of_nonempty U hUne
  have hfinComp : IsFinite ((g ≫ ν) ∣_ U) := by rwa [hgν]
  rw [morphismRestrict_comp] at hfinComp
  refine ⟨g, hgν, inferInstance, hdom, inferInstance, ν ⁻¹ᵁ U,
    ⟨⟨genericPoint (Y.normalizationScheme hY), ?_⟩⟩, IsFinite.comp_iff.mp hfinComp⟩
  show ν (genericPoint (Y.normalizationScheme hY)) ∈ U
  rw [hνgen]
  exact hηU

/-! ### Finiteness of the singular locus -/

/-- A scheme is regular iff it is locally Noetherian with regular local rings. -/
private theorem isRegular_iff_isLocallyNoetherian_and_forall_stalk (X : Scheme.{u}) :
    IsRegular X ↔ IsLocallyNoetherian X ∧ ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x) :=
  (isRegular_tfae X).out 1 2 (by simp) (by simp)

/-- On a scheme of dimension at most two a point whose local ring has dimension greater than one
is a closed point: its coheight is already maximal, so nothing specializes to it properly. -/
private theorem isClosed_singleton_of_one_lt_ringKrullDim_stalk (Y : Scheme.{u})
    (hdim : topologicalKrullDim Y ≤ 2) (y : Y)
    (hy : 1 < ringKrullDim (Y.presheaf.stalk y)) : IsClosed ({y} : Set Y) := by
  have hbound (z : Y) : Order.coheight z ≤ 2 := by
    have h := Order.coheight_le_krullDim z
    rw [← Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := Y))] at h
    exact WithBot.coe_le_coe.mp (h.trans hdim)
  have hy' : 1 < Order.coheight y := by
    rw [ringKrullDim_stalk_eq_coheight] at hy
    exact_mod_cast hy
  have hy2 : Order.coheight y = 2 :=
    le_antisymm (hbound y) ((ENat.add_one_le_iff (by simp : (1 : ℕ∞) ≠ ⊤)).mpr hy')
  refine isClosed_of_closure_subset fun z hz => ?_
  have hzy : z ≤ y := specializes_iff_mem_closure.mpr hz
  refine Set.mem_singleton_iff.mpr ?_
  by_contra hne
  have hlt := Order.coheight_strictAnti (show z < y from ⟨hzy, fun hyz =>
      hne ((hyz : Specializes z y).antisymm (hzy : Specializes y z)).eq⟩)
    (lt_of_le_of_lt (hbound y) (by decide : (2 : ℕ∞) < ⊤))
  rw [hy2] at hlt
  exact (not_lt_of_ge (hbound z)) hlt

/-- Over a normal base of dimension at most one at the image point, an injective map of local
rings induced by a morphism with integral source is flat: the base local ring is Dedekind and the
source local ring is torsion-free over it. -/
private theorem flat_stalkMap_of_injective_of_ringKrullDim_stalk_le_one {X Y : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian Y] [IsNormal Y] (f : X ⟶ Y) (x : X)
    (hinj : Function.Injective (f.stalkMap x).hom)
    (hdim : ringKrullDim (Y.presheaf.stalk (f x)) ≤ 1) :
    (f.stalkMap x).hom.Flat := by
  let R := Y.presheaf.stalk (f x)
  let S := X.presheaf.stalk x
  let : Algebra R S := (f.stalkMap x).hom.toAlgebra
  have : IsIntegrallyClosed R := IsNormal.stalk_normal (f x)
  have : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr hdim
  have : Ring.DimensionLEOne R := ⟨fun hne hp => hp.isMaximal_of_ne_bot hne⟩
  have : IsDedekindDomain R :=
    { (inferInstance : IsDomain R), (inferInstance : IsNoetherianRing R),
      (inferInstance : Ring.DimensionLEOne R), (inferInstance : IsIntegrallyClosed R) with }
  have : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hinj
  have : Module.Flat R S := IsDedekindDomain.flat_iff_torsion_eq_bot.mpr
    (Submodule.isTorsionFree_iff_torsion_eq_bot.mp inferInstance)
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

/-- **A normal Noetherian integral scheme of dimension at most two admitting an alteration by a
regular scheme has a finite singular locus.** Away from the locus where the morphism fails to be
flat the local rings of the base are regular, by descent of regularity along a flat local
homomorphism; that locus is closed, and its image misses every point whose local ring has
dimension at most one, so every point of the image is closed and the image is finite. -/
private theorem finite_singularLocus_of_regular_alteration {X N : Scheme.{u}} [IsIntegral X]
    [IsIntegral N] [IsNoetherian N] [IsNormal N] (g : X ⟶ N) [IsProper g] [IsDominant g]
    (hreg : IsRegular X) (hdim : topologicalKrullDim N ≤ 2) : (singularLocus N).Finite := by
  have hinj := ((tfae_isDominant_of_isIntegral g).out 1 6).mp (inferInstance : IsDominant g)
  let Z : Set N := g '' {x : X | ¬ (g.stalkMap x).hom.Flat}
  have hZ : IsClosed Z :=
    g.isClosedMap _ (isOpen_setOf_isFlatAt_of_isLocallyNoetherian g).isClosed_compl
  have hlow (y : N) (hy : ringKrullDim (N.presheaf.stalk y) ≤ 1) : y ∉ Z := by
    rintro ⟨x, hx, rfl⟩
    exact hx (flat_stalkMap_of_injective_of_ringKrullDim_stalk_le_one g x (hinj x) hy)
  have hfinite : Z.Finite := finite_of_isClosed_of_forall_isClosed_singleton hZ fun y hy =>
    isClosed_singleton_of_one_lt_ringKrullDim_stalk N hdim y
      (lt_of_not_ge fun h => hlow y h hy)
  refine hfinite.subset fun y hy => ?_
  by_contra hyZ
  obtain ⟨x, rfl⟩ := g.surjective y
  have hflat : (g.stalkMap x).hom.Flat := of_not_not fun h => hyZ ⟨x, h, rfl⟩
  have : IsRegularLocalRing (X.presheaf.stalk x) :=
    ((isRegular_iff_isLocallyNoetherian_and_forall_stalk X).mp hreg).2 x
  let : Algebra (N.presheaf.stalk (g x)) (X.presheaf.stalk x) :=
    (g.stalkMap x).hom.toAlgebra
  have : Module.Flat (N.presheaf.stalk (g x)) (X.presheaf.stalk x) := hflat
  have : IsLocalHom (algebraMap (N.presheaf.stalk (g x)) (X.presheaf.stalk x)) :=
    g.toLRSHom.prop x
  exact hy (IsRegularLocalRing.of_flat_of_isLocalHom (X.presheaf.stalk x))

/-! ### Normality of the completed local rings -/

/-- Regularity descends along a flat preimmersion onto a locally Noetherian scheme: such a
morphism induces isomorphisms on local rings. -/
private theorem isRegular_of_flat_isPreimmersion {X Y : Scheme.{u}} (i : Y ⟶ X) [Flat i]
    [IsPreimmersion i] (hY : IsLocallyNoetherian Y) (hX : IsRegular X) : IsRegular Y := by
  obtain ⟨-, hregX⟩ := (isRegular_iff_isLocallyNoetherian_and_forall_stalk X).mp hX
  refine (isRegular_iff_isLocallyNoetherian_and_forall_stalk Y).mpr ⟨hY, fun y => ?_⟩
  have : IsIso (i.stalkMap y) := isIso_stalkMap_of_flat_isPreimmersion i y
  have : IsRegularLocalRing (X.presheaf.stalk (i y)) := hregX (i y)
  exact IsRegularLocalRing.of_ringEquiv (asIso (i.stalkMap y)).commRingCatIsoToRingEquiv

/-- Integrality descends along a flat preimmersion with nonempty source onto an integral scheme:
the local rings are preserved, so the source is reduced, and a generic point of the target lifts
because a flat morphism lifts specializations. -/
private theorem isIntegral_of_flat_isPreimmersion {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    [IsPreimmersion f] [IsIntegral Y] [Nonempty X] : IsIntegral X := by
  have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
    have := isIso_stalkMap_of_flat_isPreimmersion f x
    exact isReduced_of_injective (inv (f.stalkMap x)).hom
      (ConcreteCategory.bijective_of_isIso _).1
  have : IsReduced X := isReduced_of_isReduced_stalk X
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨η, -, hη⟩ := Flat.generalizingMap f (genericPoint_specializes (f x))
  have hgen : IsGenericPoint η (Set.univ : Set X) := by
    refine Set.eq_univ_iff_forall.mpr fun z => ?_
    refine specializes_iff_mem_closure.mp (f.isEmbedding.isInducing.specializes_iff.mp ?_)
    rw [hη]
    exact genericPoint_specializes (f z)
  have : IrreducibleSpace X := (irreducibleSpace_def X).mpr hgen.isIrreducible
  exact isIntegral_of_irreducibleSpace_of_isReduced X

/-- Finiteness over an open subset of the base is inherited by a base change: the restriction of
the second projection over the preimage of that open is a base change of the restriction. -/
private theorem isFinite_morphismRestrict_pullback_snd {X Y S : Scheme.{u}} (f : X ⟶ S)
    (g : Y ⟶ S) (U : S.Opens) (hf : IsFinite (f ∣_ U)) :
    IsFinite (Limits.pullback.snd f g ∣_ (g ⁻¹ᵁ U)) := by
  have heq : Limits.pullback.snd f g ⁻¹ᵁ (g ⁻¹ᵁ U) =
      Limits.pullback.snd f g ⁻¹ᵁ (g ⁻¹ᵁ U) ⊓ Limits.pullback.fst f g ⁻¹ᵁ (f ⁻¹ᵁ U) := by
    have hpre := congrArg (fun a : Limits.pullback f g ⟶ S => a ⁻¹ᵁ U)
      (Limits.pullback.condition (f := f) (g := g))
    simp only [Scheme.Hom.comp_preimage] at hpre
    rw [← hpre]
    simp
  have H := Scheme.Hom.isPullback_resLE (IsPullback.of_hasPullback f g).flip
    (US := U) le_rfl le_rfl heq
  have hres : IsFinite (f.resLE U (f ⁻¹ᵁ U) le_rfl) := by
    simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using hf
  have hbase := MorphismProperty.of_isPullback (P := @IsFinite) H.flip hres
  simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using hbase

/-- **The base change of an alteration by a regular scheme to the spectrum of a local ring of
the target is again an alteration by a regular scheme.** The morphism out of the spectrum of a
local ring is a flat preimmersion, so the first projection of the fibre product is one too; that
makes the fibre product integral and regular, and properness, dominance and generic finiteness
are inherited from the alteration by base change. -/
private theorem isAlteration_pullback_fromSpecStalk {X Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] (f : X ⟶ Y) (hf : IsAlteration f) (hX : IsRegular X) (y : Y) :
    IsAlteration (Limits.pullback.snd f (Y.fromSpecStalk y)) ∧
      IsRegular (Limits.pullback f (Y.fromSpecStalk y) : Scheme.{u}) := by
  let i := Y.fromSpecStalk y
  let p : Limits.pullback f i ⟶ X := Limits.pullback.fst f i
  let q : Limits.pullback f i ⟶ Spec (Y.presheaf.stalk y) := Limits.pullback.snd f i
  have : IsProper f := hf.1
  have : IsDominant f := hf.2.1
  have : IsIntegral X := hf.2.2.1
  have : Surjective f := Surjective.of_universallyClosed_of_isDominant f
  have : Flat i := flat_fromSpecStalk Y y
  have : Surjective q := MorphismProperty.of_isPullback (P := @Surjective)
    (IsPullback.of_hasPullback f i) inferInstance
  have : Nonempty (Limits.pullback f i : Scheme.{u}) := by
    obtain ⟨z, -⟩ := q.surjective (IsLocalRing.closedPoint (Y.presheaf.stalk y))
    exact ⟨z⟩
  have hZ : IsIntegral (Limits.pullback f i : Scheme.{u}) := isIntegral_of_flat_isPreimmersion p
  have hregular : IsRegular (Limits.pullback f i : Scheme.{u}) :=
    isRegular_of_flat_isPreimmersion p (LocallyOfFiniteType.isLocallyNoetherian q) hX
  refine ⟨⟨inferInstance, inferInstance, hZ, ?_⟩, hregular⟩
  obtain ⟨U, hU, hfinite⟩ := hf.2.2.2
  have hηU : genericPoint Y ∈ U := genericPoint_mem_of_nonempty U hU
  obtain ⟨η, hη⟩ : genericPoint Y ∈ Set.range i := by
    rw [Scheme.range_fromSpecStalk]
    exact genericPoint_specializes y
  refine ⟨i ⁻¹ᵁ U, ⟨⟨η, ?_⟩⟩, isFinite_morphismRestrict_pullback_snd f i U hfinite⟩
  show i η ∈ U
  rwa [hη]

/-- **The local rings of a normal scheme with an alteration by a regular scheme have normal
completions.** The local ring `A` at a point is a normal Noetherian local domain, and the base
change of the alteration to `Spec A` is again an alteration by a regular scheme, so
[Stacks, Tag 0BGI] makes the completion of the integral closure `B` of `A` in `Frac(A)` normal
and `B` a finite `A`-module; [Stacks, Tag 0BGH] applied to the pair `A ⊆ B` of finite
`A`-algebras then makes the completion of `A` itself normal. -/
private theorem isNormalRing_adicCompletion_stalk_of_regular_alteration {X N : Scheme.{u}}
    [IsIntegral N] [IsLocallyNoetherian N] [IsNormal N] (g : X ⟶ N) (hg : IsAlteration g)
    (hreg : IsRegular X) (y : N) :
    IsNormalRing (AdicCompletion (IsLocalRing.maximalIdeal (N.presheaf.stalk y))
      (N.presheaf.stalk y)) := by
  let A := N.presheaf.stalk y
  have : IsDomain A := IsNormal.stalk_isDomain y
  have : IsIntegrallyClosed A := IsNormal.stalk_normal y
  obtain ⟨halt, hregZ⟩ := isAlteration_pullback_fromSpecStalk g hg hreg y
  have hBinj : Function.Injective (algebraMap A ↥(integralClosure A (FractionRing A))) :=
    fun a b hab => IsFractionRing.injective A (FractionRing A) (congrArg Subtype.val hab)
  have : Module.Finite A ↥(integralClosure A (FractionRing A)) :=
    module_finite_integralClosure_of_regular_alteration A _
      (Limits.pullback.snd g (N.fromSpecStalk y)) halt hregZ
  have hcompletion := isNormalRing_adicCompletion_of_finite_injective A A
    ↥(integralClosure A (FractionRing A)) hBinj (IsNormalRing.of_isIntegrallyClosed A)
    (isNormalRing_adicCompletion_integralClosure_of_regular_alteration A _
      (Limits.pullback.snd g (N.fromSpecStalk y)) halt hregZ)
  have hid : (IsLocalRing.maximalIdeal A).map (algebraMap A A) =
      IsLocalRing.maximalIdeal A := by simp
  rwa [hid] at hcompletion

/-! ### The criterion on the normalization -/

/-- **A two-dimensional integral Noetherian scheme with an alteration by a regular scheme has
finite normalization, whose singular locus is finite and whose local rings there have normal
completions.** This is the implication `(1) ⇒ (4)` of the theorem on resolution of
two-dimensional schemes.

Finiteness of the normalization `ν : Y^ν ⟶ Y` is [Stacks, Tag 0BGG]. The alteration factors
through `ν` because its regular source is normal, and the lift is again an alteration, so the
remaining two assertions are the statements about a normal integral Noetherian scheme of
dimension at most two carrying an alteration by a regular scheme: its singular locus is
contained in the image of the non-flat locus of the alteration, which is closed and consists of
closed points; and the completion of each of its local rings is normal by [Stacks, Tags 0BGI and
0BGH]. -/
theorem finite_normalization_and_normal_completions_of_exists_regular_alteration
    (Y : Scheme.{u}) [IsIntegral Y] [IsNoetherian Y]
    (hY : ∀ U : Y.Opens, IsCompact (U : Set Y) → (irreducibleComponents U).Finite)
    (hdim : topologicalKrullDim Y = 2)
    (hres : ∃ (X : Scheme.{u}) (f : X ⟶ Y), IsAlteration f ∧ IsRegular X) :
    IsFinite (Scheme.normalization Y hY) ∧
      (singularLocus (Y.normalizationScheme hY)).Finite ∧
      ∀ y : Y.normalizationScheme hY, y ∈ singularLocus (Y.normalizationScheme hY) →
        IsNormalRing (AdicCompletion
          (IsLocalRing.maximalIdeal ((Y.normalizationScheme hY).presheaf.stalk y))
          ((Y.normalizationScheme hY).presheaf.stalk y)) := by
  obtain ⟨X, f, hf, hreg⟩ := hres
  have hfin : IsFinite (Scheme.normalization Y hY) :=
    normalization_isFinite_of_regular_alteration Y X f hf hreg
  let ν := Scheme.normalization Y hY
  have : IsFinite ν := hfin
  have : IsNormal (Y.normalizationScheme hY) := Scheme.isNormal_normalizationScheme Y hY
  have : IsLocallyNoetherian (Y.normalizationScheme hY) :=
    LocallyOfFiniteType.isLocallyNoetherian ν
  have : CompactSpace (Y.normalizationScheme hY) := QuasiCompact.compactSpace_of_compactSpace ν
  have : IsNoetherian (Y.normalizationScheme hY) := {}
  have hdimN : topologicalKrullDim (Y.normalizationScheme hY) ≤ 2 :=
    (topologicalKrullDim_le_of_isIntegralHom ν).trans_eq hdim
  obtain ⟨g, -, hg⟩ := exists_isAlteration_lift_normalization Y hY X f hf hreg hfin
  have : IsProper g := hg.1
  have : IsDominant g := hg.2.1
  have : IsIntegral X := hg.2.2.1
  exact ⟨hfin, finite_singularLocus_of_regular_alteration g hreg hdimN,
    fun y _ => isNormalRing_adicCompletion_stalk_of_regular_alteration g hg hreg y⟩

end AlgebraicGeometry

end
