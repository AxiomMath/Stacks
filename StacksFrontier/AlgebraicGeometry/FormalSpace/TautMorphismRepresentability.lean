module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableLocalOnSourceAndTarget
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Types
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.LocallySurjectiveTransfer
public import StacksFrontier.Topology.Algebra.AdicTopology.Taut

/-!
# Taut ring maps and representability by algebraic spaces

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a morphism of
locally countably indexed formal algebraic spaces over `S`. **Stacks 0ANK** says that the
following are equivalent:

1. every commutative square with affine formal algebraic spaces `U`, `V` and representable
   étale maps `U ⟶ X`, `V ⟶ Y` has its upper horizontal map `U ⟶ V` given by a taut
   continuous homomorphism of countably indexed weakly admissible topological rings;
2. there is a covering `{Vⱼ ⟶ Y}` as in Definition 0AIM and for each `j` a covering
   `{Uᵢ ⟶ Vⱼ ×_Y X}` as in Definition 0AIM with each `Uᵢ ⟶ Vⱼ` given by such a taut map;
3. there is a covering `{Uᵢ ⟶ X}` as in Definition 0AIM and for each `i` a factorization
   `Uᵢ ⟶ Vᵢ ⟶ Y` through an affine formal algebraic space representable étale over `Y` with
   `Uᵢ ⟶ Vᵢ` given by such a taut map;
4. `f` is representable by algebraic spaces.

## Main definitions

* `AlgebraicGeometry.FormalSpace.TautChartProperty`: tautness of a continuous homomorphism,
  in the shape in which the local-property machinery of Stacks 0ANG takes a property of ring
  maps.
* `AlgebraicGeometry.FormalSpace.IsTautOnEveryAffineEtaleDiagram`,
  `AlgebraicGeometry.FormalSpace.IsTautAfterTargetCover` and
  `AlgebraicGeometry.FormalSpace.IsTautAfterSourceCover`: conditions (1), (2) and (3) of
  **Stacks 0ANK**, that is the three conditions of Stacks 0ANG at the class of countably
  indexed weakly admissible topological rings and the property of being taut.

## Main results

* `AlgebraicGeometry.FormalSpace.hasPropertyAfterSourceCover_of_afterTargetCover`:
  **Stacks 0ANG**, the implication from condition (2) to condition (3), for an arbitrary class
  of rings and property of ring maps.
* `AlgebraicGeometry.FormalSpace.isTaut_tfae_isRepresentableByAlgebraicSpaces`:
  **Stacks 0ANK**.

## Implementation notes

The implication from condition (2) to condition (3) holds for any class `C` and property `P`
and is proved here in that generality: the coverings of condition (2) compose to a covering
`{Uᵢ ⟶ Vⱼ ×_Y X ⟶ X}` of the source indexed by the pairs, each member of which factors
through the chart `Vⱼ` of the target by the very map condition (2) puts `P` on. Joint
surjectivity of the composed family is the only point needing an argument: the family of
projections `{Vⱼ ×_Y X ⟶ X}` is jointly surjective by
`CategoryTheory.Sheaf.isLocallySurjective_sigmaDesc_pullback_snd`, and the comparison map from
the coproduct over the pairs to the coproduct over `j` is an epimorphism because each
`∐ᵢ Uᵢ ⟶ Vⱼ ×_Y X` is one.

The source deduces the equivalence of (1), (2) and (3) from Stacks 0ANG, whose hypothesis that
tautness be a local property is Stacks 0ANJ, and then compares with (4) through Stacks 0AN5 and
Stacks 0AN4. The route taken here closes the cycle `(1) ⟹ (2) ⟹ (3) ⟹ (4) ⟹ (1)` instead,
which needs neither the implication (3) ⟹ (1) of Stacks 0ANG nor its locality hypothesis: the
step (3) ⟹ (4) is Stacks 0AN5 followed by Stacks 0AN4, and the step (4) ⟹ (1) is Stacks 0AN4
followed by Stacks 0AN5.

Five inputs of the source are explicit hypotheses because the library does not carry them, in
the same shape as for Stacks 0ANG and Stacks 0AN4 themselves.

* `h0AJ3` is Stacks 0AJ3, that the fibre product of a chart of the target with `f` is a formal
  algebraic space; it is the hypothesis `hpb` of
  `AlgebraicGeometry.FormalSpace.hasPropertyAfterTargetCover_of_everyAffineEtaleDiagram`.
* `h0AKX` is the implication (2) ⟹ (1) of Stacks 0AKX for the countably indexed property: an
  affine formal algebraic space representable étale over a locally countably indexed formal
  algebraic space is countably indexed. The library takes condition (2) as the definition of
  "locally countably indexed" precisely because that equivalence is missing, so the charts
  appearing in (1), (2) and (3) are not known to be countably indexed without it.
* `h0AN5` is Stacks 0AN5, the equivalence of its conditions (1) and (3), read on countably
  indexed affine formal algebraic spaces: a map of charts is representable by algebraic spaces
  exactly when the continuous homomorphism presenting it is taut. The library carries only the
  implication (2) ⟹ (1) of Stacks 0AN5. Reading the equivalence on charts rather than on
  formal spectra uses that a countably indexed affine formal algebraic space is a formal
  spectrum (Stacks 0AIK) and that a map of formal spectra comes from a continuous
  homomorphism (Stacks 0AN0); restricting it to countably indexed charts is what keeps it
  faithful, since an affine formal algebraic space which is not a formal spectrum has no
  presentation at all and the condition on its chart maps is then vacuous.
* `h0AQ0` is Stacks 0AQ0; it is the hypothesis of the same name of
  `AlgebraicGeometry.FormalSpace.isRepresentableOnEverySquare_of_isRepresentable`.
* `h0AN4` is the implication (5) ⟹ (1) of Stacks 0AN4: a morphism of formal algebraic spaces
  admitting a covering of its source by charts which factor through charts of the target by
  morphisms representable by algebraic spaces is itself representable by algebraic spaces. The
  library carries the implications (1) ⟹ (2), (1) ⟹ (3) and (3) ⟹ (4) of Stacks 0AN4, none of
  which returns representability of `f`.

## References

* [Stacks Project, Tag 0AIK](https://stacks.math.columbia.edu/tag/0AIK)
* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AJ3](https://stacks.math.columbia.edu/tag/0AJ3)
* [Stacks Project, Tag 0AKX](https://stacks.math.columbia.edu/tag/0AKX)
* [Stacks Project, Tag 0AN0](https://stacks.math.columbia.edu/tag/0AN0)
* [Stacks Project, Tag 0AN4](https://stacks.math.columbia.edu/tag/0AN4)
* [Stacks Project, Tag 0AN5](https://stacks.math.columbia.edu/tag/0AN5)
* [Stacks Project, Tag 0ANG](https://stacks.math.columbia.edu/tag/0ANG)
* [Stacks Project, Tag 0ANJ](https://stacks.math.columbia.edu/tag/0ANJ)
* [Stacks Project, Tag 0ANK](https://stacks.math.columbia.edu/tag/0ANK)
* [Stacks Project, Tag 0AQ0](https://stacks.math.columbia.edu/tag/0AQ0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Composing the coverings of condition (2) into a covering of the source -/

section LocalProperty

variable (C : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R], Prop)
  (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
    [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)

/-- **Stacks 0ANG, condition (2) implies condition (3).** A covering of the target together
with coverings of the fibre products of its members with the source compose to a covering of
the source whose members factor through the chart of the target they came from, by the map
condition (2) puts `P` on. -/
@[stacks 0ANG "condition (2) implies condition (3)"]
theorem hasPropertyAfterSourceCover_of_afterTargetCover {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hf : HasPropertyAfterTargetCover B S hS C P f) :
    HasPropertyAfterSourceCover B S hS C P f := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨J, V, v, ⟨hVaffine, hVetale, hVsurj⟩, hcharts⟩ := hf
  choose I U w hUcover hUproperty using hcharts
  refine ⟨(j : J) × I j, fun p ↦ U p.1 p.2, fun p ↦ w p.1 p.2 ≫ pullback.snd (v p.1) f,
    ⟨fun p ↦ (hUcover p.1).1 p.2, fun p ↦ IsRepresentableEtale.comp B S hS
      ((hUcover p.1).2.1 p.2)
      (isRepresentableEtale_pullback_snd B S hS (v p.1) f (hVetale p.1)), ?_⟩,
    fun p ↦ ⟨V p.1, v p.1, w p.1 p.2 ≫ pullback.fst (v p.1) f, hVaffine p.1, hVetale p.1,
      by rw [Category.assoc, Category.assoc, ← pullback.condition], hUproperty p.1 p.2⟩⟩
  have hepi : ∀ j, Epi (Sigma.desc (w j)) := fun j ↦
    (Sheaf.isLocallySurjective_iff_epi _).1 (hUcover j).2.2
  have hepiSnd : Epi (Sigma.desc fun j ↦ pullback.snd (v j) f) :=
    (Sheaf.isLocallySurjective_iff_epi _).1
      (Sheaf.isLocallySurjective_sigmaDesc_pullback_snd f v hVsurj)
  have hrepi : Epi (Sigma.desc fun p : (j : J) × I j ↦
      w p.1 p.2 ≫ Sigma.ι (fun j ↦ pullback (v j) f) p.1) := by
    refine ⟨fun {Z} a b hab ↦ Sigma.hom_ext _ _ fun j ↦ ?_⟩
    have := hepi j
    refine (cancel_epi (Sigma.desc (w j))).1 (Sigma.hom_ext _ _ fun i ↦ ?_)
    simpa using congrArg
      (fun z ↦ Sigma.ι (fun p : (j : J) × I j ↦ U p.1 p.2) ⟨j, i⟩ ≫ z) hab
  have hfac : (Sigma.desc fun p : (j : J) × I j ↦
        w p.1 p.2 ≫ Sigma.ι (fun j ↦ pullback (v j) f) p.1) ≫
      (Sigma.desc fun j ↦ pullback.snd (v j) f) =
      Sigma.desc fun p : (j : J) × I j ↦ w p.1 p.2 ≫ pullback.snd (v p.1) f :=
    Sigma.hom_ext _ _ fun p ↦ by simp
  refine (Sheaf.isLocallySurjective_iff_epi _).2 ?_
  rw [← hfac]
  exact epi_comp _ _

end LocalProperty

/-! ### Stacks 0ANK -/

/-- Tautness of a continuous homomorphism of topological rings, in the shape in which the
local-property machinery of Stacks 0ANG takes a property of ring maps. -/
abbrev TautChartProperty : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁]
    [IsTopologicalRing R₁] [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂],
    (R₁ →+* R₂) → Prop :=
  fun {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
    [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂] (φ : R₁ →+* R₂) ↦
    RingHom.IsTaut φ

/-- **Stacks 0ANK, condition (1).** Every commutative square whose vertical maps are
representable étale maps from affine formal algebraic spaces has its upper horizontal map
given by a taut continuous homomorphism of countably indexed weakly admissible topological
rings. -/
abbrev IsTautOnEveryAffineEtaleDiagram {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsCountablyWeaklyAdmissible
    TautChartProperty f

/-- **Stacks 0ANK, condition (2).** There is an affine étale covering of the target and, for
each of its members, an affine étale covering of the fibre product of that member with the
source on which the maps to that member are taut. -/
abbrev IsTautAfterTargetCover {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  HasPropertyAfterTargetCover B S hS TopologicalRing.IsCountablyWeaklyAdmissible
    TautChartProperty f

/-- **Stacks 0ANK, condition (3).** There is an affine étale covering of the source, each
member of which factors through an affine formal algebraic space representable étale over the
target by a taut map. -/
abbrev IsTautAfterSourceCover {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  HasPropertyAfterSourceCover B S hS TopologicalRing.IsCountablyWeaklyAdmissible
    TautChartProperty f

/-- **Stacks 0ANK.** Let `f : X ⟶ Y` be a morphism of locally countably indexed formal
algebraic spaces over `S`. The following are equivalent:

1. every commutative square with affine formal algebraic spaces `U`, `V` and representable
   étale maps `U ⟶ X`, `V ⟶ Y` has `U ⟶ V` given by a taut continuous homomorphism of
   countably indexed weakly admissible topological rings;
2. there is a covering `{Vⱼ ⟶ Y}` as in Definition 0AIM and for each `j` a covering
   `{Uᵢ ⟶ Vⱼ ×_Y X}` as in Definition 0AIM with each `Uᵢ ⟶ Vⱼ` given by such a taut map;
3. there is a covering `{Uᵢ ⟶ X}` as in Definition 0AIM and for each `i` a factorization
   `Uᵢ ⟶ Vᵢ ⟶ Y` through an affine formal algebraic space representable étale over `Y` with
   `Uᵢ ⟶ Vᵢ` given by such a taut map;
4. `f` is representable by algebraic spaces.

The cycle runs `(1) ⟹ (2) ⟹ (3) ⟹ (4) ⟹ (1)`: the first step is Stacks 0ANG, the second is
proved here, and the last two pass between tautness and representability on charts through
Stacks 0AN5 and between charts and `f` through Stacks 0AN4. -/
@[stacks 0ANK "the equivalence, with the five inputs this library does not carry as named \
hypotheses: Stacks 0AJ3 as h0AJ3, the implication (2) implies (1) of Stacks 0AKX for the \
countably indexed property as h0AKX, the equivalence of conditions (1) and (3) of Stacks 0AN5 \
read on countably indexed affine charts as h0AN5, Stacks 0AQ0 as h0AQ0, and the implication \
(5) implies (1) of Stacks 0AN4 as h0AN4"]
theorem isTaut_tfae_isRepresentableByAlgebraicSpaces {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsLocallyCountablyIndexed B S hS X) (hY : IsLocallyCountablyIndexed B S hS Y)
    (h0AJ3 : ∀ (V : FppfSheaf B S hS) (v : V ⟶ Y), IsAffineFormalAlgebraicSpace B S hS V →
      IsRepresentableEtale B S hS v → IsFormalAlgebraicSpace B S hS (pullback v f))
    (h0AKX : ∀ (Z : FppfSheaf B S hS), IsLocallyCountablyIndexed B S hS Z →
      ∀ (U : FppfSheaf B S hS) (a : U ⟶ Z), IsAffineFormalAlgebraicSpace B S hS U →
      IsRepresentableEtale B S hS a → IsCountablyIndexed B S hS U)
    (h0AN5 : ∀ {U V : FppfSheaf B S hS} (t : U ⟶ V),
      IsAffineFormalAlgebraicSpace B S hS U → IsAffineFormalAlgebraicSpace B S hS V →
      IsCountablyIndexed B S hS U → IsCountablyIndexed B S hS V →
      (Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS t.hom ↔
        HasPropertyOnAffineChartMap B S hS TopologicalRing.IsCountablyWeaklyAdmissible
          TautChartProperty t))
    (h0AQ0 : ∀ {A A' A'' : FppfSheaf B S hS} (s : A ⟶ A') (r : A' ⟶ A''),
      IsFormalAlgebraicSpace B S hS A → IsFormalAlgebraicSpace B S hS A' →
      IsFormalAlgebraicSpace B S hS A'' →
      Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (s ≫ r).hom →
      Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS s.hom)
    (h0AN4 : ∀ (I : Type (u + 1)) (U W : I → FppfSheaf B S hS) (a : ∀ i, U i ⟶ X)
      (b : ∀ i, W i ⟶ Y) (t : ∀ i, U i ⟶ W i), IsAffineEtaleCover B S hS U a →
      (∀ i, IsAffineFormalAlgebraicSpace B S hS (W i)) →
      (∀ i, Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (b i).hom) →
      (∀ i, Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (t i).hom) →
      (∀ i, a i ≫ f = t i ≫ b i) →
      Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom) :
    List.TFAE
      [ IsTautOnEveryAffineEtaleDiagram B S hS f,
        IsTautAfterTargetCover B S hS f,
        IsTautAfterSourceCover B S hS f,
        Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom ] := by
  tfae_have 1 → 2 := fun h ↦
    hasPropertyAfterTargetCover_of_everyAffineEtaleDiagram B S hS
      TopologicalRing.IsCountablyWeaklyAdmissible TautChartProperty f hY.1 h0AJ3 h
  tfae_have 2 → 3 := fun h ↦
    hasPropertyAfterSourceCover_of_afterTargetCover B S hS
      TopologicalRing.IsCountablyWeaklyAdmissible TautChartProperty f h
  tfae_have 3 → 4 := by
    rintro ⟨I, U, a, hUcover, hfac⟩
    choose W b t hWaffine hWetale hWsquare hWproperty using hfac
    refine h0AN4 I U W a b t hUcover hWaffine (fun i ↦ (hWetale i).1) (fun i ↦ ?_) hWsquare
    exact (h0AN5 (t i) (hUcover.1 i) (hWaffine i)
      (h0AKX X hX (U i) (a i) (hUcover.1 i) (hUcover.2.1 i))
      (h0AKX Y hY (W i) (b i) (hWaffine i) (hWetale i))).2 (hWproperty i)
  tfae_have 4 → 1 := by
    intro hf U V a b t hU hV ha hb hsq
    refine (h0AN5 t hU hV (h0AKX X hX U a hU ha) (h0AKX Y hY V b hV hb)).1 ?_
    exact isRepresentableOnEverySquare_of_isRepresentable B S hS f hY.1 h0AQ0 hf U V a b t
      (isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS hU)
      (isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS hV) ha.1 hb.1 hsq
  tfae_finish

end AlgebraicGeometry.FormalSpace

end
