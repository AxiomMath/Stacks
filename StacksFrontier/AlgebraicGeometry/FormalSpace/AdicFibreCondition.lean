module

public import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
public import Mathlib.CategoryTheory.Sites.PreservesLimits
public import Mathlib.CategoryTheory.Sites.RegularEpi
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import StacksCore.CategoryTheory.Sites.Representable.MapsFromRepresentable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.ThickeningStage
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineOfRepresentable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionAlongClosedSubsetReduction
public import StacksFrontier.AlgebraicGeometry.FormalSpace.MapsToAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductInclusion
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsOfPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.StandardCoverings
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.ObjectsAndColimits
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.Over
public import StacksFrontier.CategoryTheory.Sites.SubcanonicalSheafifiedYoneda
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.BigFppfSite
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SiteQuasiCompact
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautStageBaseChange
public import StacksFrontier.CategoryTheory.Sites.Representable.SheafifiedYonedaSubcanonical
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautStageBaseChangeStages

/-!
# The fibre of an algebraization over a closed subset

Let `S` be a scheme, `X` an algebraic space over `S` and `T ⊆ |X|` a closed subset. Let `R` be
a Noetherian complete local `S`-algebra with maximal ideal `𝔪`, presented by a quotient system
whose weak ideals of definition are cofinal among the powers of `𝔪`, and let
`p : Spf R ⟶ X_{/T}` be a morphism into the completion of `X` along `T` which is representable
by algebraic spaces. This file proves that a morphism `g : Spec R ⟶ X` restricting on `Spf R`
to the composite `Spf R ⟶ X_{/T} ⟶ X` has `g⁻¹(T) ⊆ {𝔪}`.

## Main results

* `AlgebraicGeometry.FormalSpace.pointsToScheme_eq_closedPoint_of_pointsMap_mem`: the fibre
  inclusion `g⁻¹(T) ⊆ {𝔪}`.

## Implementation notes

The argument is the one of Stacks 0GBU. Write `Z ⊆ X` for the reduced induced closed subspace
on `T`. Its inverse image along `g` is a closed subscheme `Spec (R / I)` of `Spec R`, and every
point of `Spec R` lying over `T` lies in it, so the assertion is that `𝔪` is the only prime
containing `I`. The sheaf `F = Spf R ×_{X_{/T}} Z` equals `Spf R ×_{Spec R} Spec (R / I)`,
because `X_{/T} ⟶ X` is a monomorphism; it is an algebraic space, since `p` is representable by
algebraic spaces, and it receives a representable thickening from the affine scheme
`Spec (R / (I + K))` for a weak ideal of definition `K`, so it has a quasi-compact model and
Stacks 0AIA factors `F ⟶ Spf R` through a single quotient stage `Spec (R / M)`. Comparing that
factorisation with the stages `Spec (R / (I + L))` gives `M ⊆ I + L` for every weak ideal of
definition `L`, whence `M ⊆ I` by Krull's intersection theorem and `𝔪 ^ n ⊆ I` for some `n`.

Stacks 0AIA is `AlgebraicGeometry.exists_factor_through_thickening`, which asks of the target
only the presentation itself and of its transition morphisms only that they be closed
immersions; the transition morphisms of a quotient system are thickenings, hence closed
immersions, by `AlgebraicGeometry.FormalSpace.quotientSystem_transition_isThickening`.

## References

* [Stacks Project, Tag 0GBU](https://stacks.math.columbia.edu/tag/0GBU)
* [Stacks Project, Tag 0AIA](https://stacks.math.columbia.edu/tag/0AIA)
* [Stacks Project, Tag 0AI9](https://stacks.math.columbia.edu/tag/0AI9)
* [Stacks Project, Tag 03IQ](https://stacks.math.columbia.edu/tag/03IQ)
* [Stacks Project, Tag 0GB9](https://stacks.math.columbia.edu/tag/0GB9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FormalSpace

universe u v w₁ w₂

/-! ### Krull's intersection theorem in the form the fibre condition needs -/

/-- A prime of a local ring containing a power of the maximal ideal is the maximal ideal. -/
private theorem eq_maximalIdeal_of_pow_le_prime {R : Type u} [CommRing R] [IsLocalRing R]
    (P : Ideal R) [P.IsPrime] (n : ℕ) (hpow : IsLocalRing.maximalIdeal R ^ n ≤ P) :
    P = IsLocalRing.maximalIdeal R :=
  le_antisymm (IsLocalRing.le_maximalIdeal_of_isPrime P)
    (Ideal.IsPrime.le_of_pow_le (I := IsLocalRing.maximalIdeal R) (P := P) hpow)

/-- **Krull's intersection theorem.** An ideal of a Noetherian local ring contained in every
`I + 𝔪 ^ n` is contained in `I`: its image in `R / I` lies in every power of the maximal ideal
of that ring, and those powers intersect in zero. -/
private theorem le_of_forall_le_sup_maximalIdeal_pow {R : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (I J : Ideal R)
    (h : ∀ n : ℕ, J ≤ I ⊔ IsLocalRing.maximalIdeal R ^ n) : J ≤ I := by
  by_cases hI : I = ⊤
  · simp [hI]
  let Q := R ⧸ I
  have _ : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr hI
  have _ : IsLocalRing Q := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  let m := (IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk I)
  have hm : m = IsLocalRing.maximalIdeal Q :=
    IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  have hinf : (⨅ n : ℕ, m ^ n) = ⊥ :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing m (hm ▸ (IsLocalRing.maximalIdeal.isMaximal Q).ne_top)
  intro x hx
  have hx' : Ideal.Quotient.mk I x ∈ ⨅ n : ℕ, m ^ n := by
    rw [Ideal.mem_iInf]
    intro n
    obtain ⟨y, hy, z, hz, hsum⟩ := Submodule.mem_sup.mp (h n hx)
    show Ideal.Quotient.mk I x ∈
      ((IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk I)) ^ n
    rw [← Ideal.map_pow, ← hsum, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hy, zero_add]
    exact Ideal.mem_map_of_mem _ hz
  rw [hinf, Ideal.mem_bot] at hx'
  exact Ideal.Quotient.eq_zero_iff_mem.mp hx'

/-- Krull's intersection theorem against a family of ideals cofinal among the powers of the
maximal ideal, rather than against the powers themselves. -/
private theorem le_of_forall_le_sup_cofinal {R : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {ι : Type*} (K : ι → Ideal R)
    (hK : ∀ n : ℕ, ∃ i, K i ≤ IsLocalRing.maximalIdeal R ^ n)
    (I J : Ideal R) (h : ∀ i, J ≤ I ⊔ K i) : J ≤ I :=
  le_of_forall_le_sup_maximalIdeal_pow I J fun n =>
    (hK n).elim fun i hi => (h i).trans (sup_le_sup_left hi I)

/-- A factorisation of one quotient spectrum of `R` through another, over `Spec R`, forces the
reverse inclusion of the two ideals. -/
private theorem ideal_le_of_quotientSpec_factorization {R : Type u} [CommRing R]
    (I J : Ideal R) (f : Spec (.of (R ⧸ I)) ⟶ Spec (.of (R ⧸ J)))
    (hf : f ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) : J ≤ I := by
  let φ : R ⧸ J →+* R ⧸ I := (Spec.preimage f).hom
  have hφ : φ.comp (Ideal.Quotient.mk J) = Ideal.Quotient.mk I := by
    have he : CommRingCat.ofHom (φ.comp (Ideal.Quotient.mk J)) =
        CommRingCat.ofHom (Ideal.Quotient.mk I) := by
      apply Spec.map_injective
      rw [CommRingCat.ofHom_comp, Spec.map_comp]
      show Spec.map (Spec.preimage f) ≫ _ = _
      rw [Spec.map_preimage]
      exact hf
    exact congrArg (fun k => k.hom) he
  intro x hx
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [← hφ]
  show φ (Ideal.Quotient.mk J x) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]

/-- If every `Spec (R / (I + K i))` of a family cofinal among the powers of the maximal ideal
maps to `Spec (R / J)` over `Spec R`, then `J ⊆ I`. -/
private theorem ideal_le_of_quotientSpec_cofinal_factorizations {R : Type u} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] {ι : Type*} (K : ι → Ideal R)
    (hK : ∀ n : ℕ, ∃ i, K i ≤ IsLocalRing.maximalIdeal R ^ n) (I J : Ideal R)
    (h : ∀ i, ∃ f : Spec (.of (R ⧸ (I ⊔ K i))) ⟶ Spec (.of (R ⧸ J)),
      f ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ⊔ K i)))) : J ≤ I :=
  le_of_forall_le_sup_cofinal K hK I J fun i =>
    (h i).elim fun f hf => ideal_le_of_quotientSpec_factorization _ _ f hf

/-- **Stacks 0AIA** with the presentation asked only to have closed-immersion transition
morphisms. A morphism to a directed colimit of sheaves represented by affine schemes of the
site, from the sheafification of the universe lift of a quasi-compact algebraic space over `S`,
factors through one of the stages.

The quasi-compact atlas of the algebraic space makes a representable sheaf map onto it by a
strong epimorphism whose source is a quasi-compact object of the site, so the composite into the
colimit factors through a stage; the colimit injections are monomorphisms, and lifting the
strong epimorphism against one of them carries the factorisation back. -/
theorem exists_factor_through_closedImmersion_stage (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (I : Type w₁) [Preorder I] [Small.{u + 1} I]
    [Nonempty I] [IsDirected I (· ≤ ·)] (D : I ⥤ BigAffineFppf B S hS)
    (hD : ∀ ⦃i j : I⦄ (g : i ⟶ j),
      _root_.AlgebraicGeometry.IsClosedImmersion ((BigAffineFppf.toScheme B S hS).map (D.map g)))
    (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (e : X ≅ colimit (D ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)))
    (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_hY : IsAlgebraicSpace B S hS Y)
    (hYqc : Space.IsQuasiCompactSpace B S hS Y)
    (f : (presheafToSheaf (BigFppfOver.topology B S hS)
      (Type (u + 1))).obj (Y ⋙ uliftFunctor.{u + 1, u}) ⟶ X) :
    ∃ i : I, ∃ g : (presheafToSheaf (BigFppfOver.topology B S hS)
        (Type (u + 1))).obj (Y ⋙ uliftFunctor.{u + 1, u}) ⟶
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
          ((BigAffineFppf.inclusion B S hS).obj (D.obj i)),
      g ≫ colimit.ι (D ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) i ≫ e.inv = f :=
  exists_factor_through_thickening' B S hS I D hD X e Y hYqc f

/-- The weak ideals of definition of a topological ring are directed under reverse
inclusion. -/
theorem weakIdeals_isDirected {R : Type u} [CommRing R] [TopologicalSpace R] :
    IsDirected (OrderDual { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I })
      (· ≤ ·) :=
  ⟨fun I K => ⟨⟨I.1 ⊓ K.1, I.2.1.inter K.2.1, fun x hx => I.2.2 x hx.1⟩,
    (show I.1 ⊓ K.1 ≤ I.1 from inf_le_left), (show I.1 ⊓ K.1 ≤ K.1 from inf_le_right)⟩⟩

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A transition morphism of a quotient system is a thickening: an element of the larger weak
ideal of definition is topologically nilpotent, hence nilpotent modulo the smaller one. -/
theorem quotientSystem_transition_isThickening {R : Type u} [CommRing R]
    [TopologicalSpace R] (D : QuotientSystem B S hS R)
    {J L : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I }} (h : J.1 ≤ L.1) :
    Stacks.Thickenings.IsThickening
      ((BigAffineFppf.toScheme B S hS).map (D.transition h)) :=
  quotientSystem_transition_isThickening' D h

/-- A stage inclusion `Spec (R / J) ⟶ Spf R` of a formal spectrum is a representable
thickening, by **Stacks 0AI9** applied to the presenting diagram of quotient spectra. -/
private theorem formalSpectrumInclusion_isThickening {R : Type u} [CommRing R]
    [TopologicalSpace R]
    [Nonempty { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I }]
    (D : QuotientSystem B S hS R)
    (J : OrderDual { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I }) :
    (MorphismProperty.relative (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
      (MorphismProperty.inverseImage
        (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) (formalSpectrumInclusion D J) :=
  formalSpectrumInclusion_isThickening' B S hS D J

/-! ### The pullback square in the value universe of the formal spectrum -/

/-- A cartesian square of presheaves of `Type u` whose bottom edge is the scheme-valued point
of an algebraic space named by a section of its sheafified universe lift becomes a cartesian
square of fppf sheaves of `Type (u + 1)`. -/
private theorem exists_isPullback_upliftedSheaf
    {X Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hZ : IsAlgebraicSpace B S hS Z) (U W : BigFppfOver B S hS) (i : W ⟶ U)
    (z : yoneda.obj W ⟶ Z) (j : Z ⟶ X) (m : upliftedSheaf Z hZ ⟶ upliftedSheaf X hX)
    (hm : m.hom = Functor.whiskerRight j uliftFunctor.{u + 1})
    (g : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U ⟶ upliftedSheaf X hX)
    (hz : IsPullback z (yoneda.map i) j
      (yonedaEquiv.symm (Sheaf.sectionEquiv (BigFppfOver.topology B S hS) g).down)) :
    ∃ z' : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj W ⟶ upliftedSheaf Z hZ,
      IsPullback z' ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map i) m g := by
  let 𝒥 := BigFppfOver.topology B S hS
  have hmj : m = (ObjectProperty.homMk (Functor.whiskerRight j uliftFunctor.{u + 1}) :
      upliftedSheaf Z hZ ⟶ upliftedSheaf X hX) :=
    (sheafToPresheaf 𝒥 (Type (u + 1))).map_injective hm
  rw [hmj]
  let L := (Functor.whiskeringRight (BigFppfOver B S hS)ᵒᵖ (Type u) (Type (u + 1))).obj
    uliftFunctor.{u + 1, u}
  let A := presheafToSheaf 𝒥 (Type (u + 1))
  let H := L ⋙ A
  let Z' := upliftedSheaf Z hZ
  let X' := upliftedSheaf X hX
  let adj := sheafificationAdjunction 𝒥 (Type (u + 1))
  have _ : IsIso adj.counit := inferInstance
  have _ : IsIso (adj.counit.app Z') := by dsimp [adj]; infer_instance
  have _ : IsIso (adj.counit.app X') := by dsimp [adj]; infer_instance
  let eZ := asIso (adj.counit.app Z')
  let eX := asIso (adj.counit.app X')
  let j' : Z' ⟶ X' := ObjectProperty.homMk (L.map j)
  let g₀ : yoneda.obj U ⟶ X := yonedaEquiv.symm (Sheaf.sectionEquiv 𝒥 g).down
  have hcanon : A.map (L.map g₀) ≫ adj.counit.app X' = g := by
    show (adj.homEquiv _ X').symm (L.map g₀) = g
    apply (adj.homEquiv _ X').symm_apply_eq.mpr
    apply uliftYonedaEquiv.injective
    show ULift.up (yonedaEquiv g₀) = Sheaf.sectionEquiv 𝒥 g
    exact ULift.ext _ _ (yonedaEquiv.apply_symm_apply _)
  refine ⟨H.map z ≫ eZ.hom, ?_⟩
  apply (hz.map H).of_iso (Iso.refl _) eZ (Iso.refl _) eX
  · exact (Category.id_comp (H.map z ≫ eZ.hom)).symm
  · simp only [Iso.refl_hom, Category.comp_id]
    rfl
  · show (((sheafToPresheaf 𝒥 (Type (u + 1))) ⋙ A).map j') ≫ adj.counit.app X' =
      adj.counit.app Z' ≫ j'
    exact adj.counit.naturality j'
  · exact hcanon

/-- The inverse image of a closed subspace of a presheaf along an `R`-point of it is a
quotient spectrum of `R`. -/
private theorem exists_quotientSpec_pullback_closedSubspace {R : Type u} [CommRing R]
    (hRS : B.Contains (Spec (.of R))) (a : Spec (.of R) ⟶ S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (Z : Subfunctor X)
    (hZ : Space.IsClosedImmersion B S hS Z.ι)
    (g : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (specOver hRS a)) ⟶ X) :
    ∃ (W : BigFppfOver B S hS)
      (i : W ⟶ (BigAffineFppf.inclusion B S hS).obj (specOver hRS a))
      (z : yoneda.obj W ⟶ Z.toFunctor),
      IsPullback z (yoneda.map i) Z.ι g ∧
      ∃ (I : Ideal R) (e : (BigFppfOver.toScheme B S hS).obj W ≅ Spec (.of (R ⧸ I))),
        (BigFppfOver.toScheme B S hS).map i =
          e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) := by
  obtain ⟨W, i, z, hs⟩ := hZ.rep g
  exact ⟨W, i, z, hs,
    _root_.AlgebraicGeometry.IsClosedImmersion.Spec_iff.mp (hZ.property g z i hs)⟩

/-! ### The fibre condition -/

attribute [local instance] Space.pointTopology

/-- **The fibre of an algebraization over a closed subset is contained in the closed point.**
Let `R` be a Noetherian complete local `S`-algebra carrying a quotient system whose weak ideals
of definition are cofinal among the powers of the maximal ideal, let `T` be a closed set of
points of an algebraic space `X` over `S`, and let `g : Spec R ⟶ X` restrict on `Spf R` to the
composite of a morphism `p : Spf R ⟶ X_{/T}` representable by algebraic spaces with
`X_{/T} ⟶ X`. Then every point of `Spec R` whose image lies in `T` is the closed point.

This is the half of the fibre condition of **Stacks 0GBU** that the source obtains from
Krull's intersection theorem. -/
public theorem pointsToScheme_eq_closedPoint_of_pointsMap_mem {R : Type u} [CommRing R]
    [TopologicalSpace R] (hR : IsNoetherianCompleteLocalRing R) (D : QuotientSystem B S hS R)
    (hD₁ : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      ∃ n : ℕ, (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n ≤ J.1)
    (hD : ∀ n : ℕ, ∃ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      J.1 ≤ (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n)
    (hRS : B.Contains (Spec (.of R))) (q : Spec (.of R) ⟶ S)
    (hq : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ q = D.overS J)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (T : Set (Space.points B S hS X)) (hT : IsClosed T)
    {P : formalSpectrum D ⟶ Space.completionSheaf B S hS X T}
    (hPadic : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS P.hom)
    {g : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
        ((BigAffineFppf.inclusion B S hS).obj (specOver hRS q)) ⟶ upliftedSheaf X hX}
    (hg : formalSpectrumToSpec D hRS q hq ≫ g = P ≫ ObjectProperty.homMk
      (Space.completionSheafToAmbient B S hS X (upliftedSheaf X hX).property T))
    (w : Space.points B S hS
      (yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (specOver hRS q))))
    (hw : Space.pointsMap B S hS
        (yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (specOver hRS q)))
        (yonedaEquiv.symm (Sheaf.sectionEquiv (BigFppfOver.topology B S hS) g).down) w ∈ T) :
    Space.pointsToScheme B S hS ((BigAffineFppf.inclusion B S hS).obj (specOver hRS q)) w =
      @IsLocalRing.closedPoint R _ hR.isLocal := by
  classical
  let _ : IsLocalRing R := hR.isLocal
  let _ : IsNoetherianRing R := hR.isNoetherian
  let 𝒴 := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  let G := BigFppfOver.toScheme B S hS
  let U := (BigAffineFppf.inclusion B S hS).obj (specOver hRS q)
  let c : Space.completionSheaf B S hS X T ⟶ upliftedSheaf X hX :=
    ObjectProperty.homMk
      (Space.completionSheafToAmbient B S hS X (upliftedSheaf X hX).property T)
  let r := formalSpectrumToSpec D hRS q hq
  let g₀ : yoneda.obj U ⟶ X :=
    yonedaEquiv.symm (Sheaf.sectionEquiv (BigFppfOver.topology B S hS) g).down
  let Zs := Space.reducedClosedSubspace B S hS X hX T hT
  have hZcl : Space.IsClosedSubspace B S hS Zs :=
    Space.isClosedSubspace_reducedClosedSubspace B S hS X hX T hT
  have hZT : Set.range (Space.pointsMap B S hS Zs.toFunctor Zs.ι) = T :=
    Space.range_pointsMap_ι_reducedClosedSubspace B S hS X hX T hT
  -- The inverse image of the reduced closed subspace along `g`.
  obtain ⟨W, i, z₀, sq, Ii, eI, heI⟩ :=
    exists_quotientSpec_pullback_closedSubspace hRS q Zs hZcl.2 g₀
  -- The given point lies in that inverse image, so `Ii` is contained in its prime.
  have hmemrange : Space.pointsMap B S hS (yoneda.obj U) g₀ w ∈
      Set.range (Space.pointsMap B S hS Zs.toFunctor Zs.ι) := by
    rw [hZT]
    exact hw
  obtain ⟨pz, hpz⟩ := hmemrange
  obtain ⟨v, -, hv⟩ := Space.exists_point_of_isPullback_presheaf B S hS sq pz w hpz
  have hrange : Space.pointsToScheme B S hS U w =
      G.map i (Space.pointsToScheme B S hS W v) := by
    rw [← hv]
    exact Space.pointsToScheme_pointsMap_yoneda B S hS i v
  have hIP : Ii ≤ (Space.pointsToScheme B S hS U w).asIdeal := by
    have hx : Ii ≤ (G.map i (Space.pointsToScheme B S hS W v)).asIdeal := by
      have heIx := congrArg (fun k : G.obj W ⟶ Spec (.of R) =>
        k (Space.pointsToScheme B S hS W v)) heI
      apply (congrArg (fun y : PrimeSpectrum R => Ii ≤ y.asIdeal) heIx).mpr
      show Ii ≤ Ideal.comap (Ideal.Quotient.mk Ii)
        (eI.hom (Space.pointsToScheme B S hS W v)).asIdeal
      intro y hy
      show Ideal.Quotient.mk Ii y ∈ (eI.hom (Space.pointsToScheme B S hS W v)).asIdeal
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hy]
      exact (eI.hom (Space.pointsToScheme B S hS W v)).asIdeal.zero_mem
    exact hrange ▸ hx
  -- The fibre product of the formal spectrum with the reduced closed subspace.
  obtain ⟨K, hK⟩ := hD 1
  rw [pow_one] at hK
  have _ : Nonempty { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I } := ⟨K⟩
  have _ : IsDirected (OrderDual { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I })
      (· ≤ ·) := TopologicalRing.isDirected_weakIdealOfDefinitionIndex R
  let Zc := reducedClosedSubsetToCompletionSheaf B S hS hX T hT
  have hZc : (Zc ≫ c).hom = Functor.whiskerRight Zs.ι uliftFunctor.{u + 1} :=
    reducedClosedSubsetToCompletionSheaf_comp_completionSheafToAmbient B S hS hX T hT
  have hcmono : Mono c :=
    (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))).mono_of_mono_map
      (show Mono c.hom from
        Space.mono_completionSheafToAmbient B S hS X (upliftedSheaf X hX).property T)
  let _ := hcmono
  let F := pullback P Zc
  have hpb : IsPullback (pullback.fst P Zc) (pullback.snd P Zc) (P ≫ c) (Zc ≫ c) := by
    simpa only [Category.comp_id] using (IsPullback.of_hasPullback P Zc).paste_vert
      (IsPullback.of_vert_isIso_mono (fst := Zc) (snd := 𝟙 _) (f := c) (g := Zc ≫ c)
        ⟨by simp⟩)
  obtain ⟨wS, hwS'⟩ :=
    exists_isPullback_upliftedSheaf hX hZcl.1 U W i z₀ Zs.ι (Zc ≫ c) hZc g sq
  have hrg : r ≫ g = P ≫ c := hg
  let b : F ⟶ 𝒴.obj W := hwS'.lift (pullback.snd P Zc) (pullback.fst P Zc ≫ r) (by
    rw [Category.assoc, hrg]
    exact hpb.w.symm)
  have hb : IsPullback (pullback.fst P Zc) b r (𝒴.map i) := by
    have hpb' : IsPullback (pullback.snd P Zc) (pullback.fst P Zc) (Zc ≫ c) (r ≫ g) := by
      rw [hrg]
      exact hpb.flip
    exact (hpb'.of_right' hwS').flip
  -- `F` is an algebraic space in the value universe of the formal spectrum.
  have hFalg : Space.IsAlgebraicSpaceULift.{u + 1} B S hS F.obj := by
    have hsq := (IsPullback.of_hasPullback P Zc).map
      (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    have hZ' : Space.IsAlgebraicSpaceULift.{u + 1} B S hS
        (reducedClosedSubsetSheaf B S hS hX T hT).obj :=
      (Space.isAlgebraicSpaceULift_comp_uliftFunctor_iff B S hS Zs.toFunctor).mpr hZcl.1
    have hpbalg : Space.IsAlgebraicSpaceULift.{u + 1} B S hS (pullback Zc.hom P.hom) :=
      Space.isAlgebraicSpaceULift_pullback_of_isRepresentableULift B S hS P.hom Zc.hom
        hPadic hZ'
    exact Space.isAlgebraicSpaceULift_of_iso B S hS
      (hsq.flip.isoIsPullback _ _ (IsPullback.of_hasPullback Zc.hom P.hom)).symm hpbalg
  -- A representable thickening into `F` from the affine scheme `Spec (R / (Ii + K))`.
  have hYpres : PreservesLimitsOfShape WalkingCospan 𝒴 := by
    dsimp [𝒴, Sheaf.sheafifiedYoneda]
    infer_instance
  let _ := hYpres
  let kk : ∀ L : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I }, _ ⟶ U :=
    fun L => (BigAffineFppf.inclusion B S hS).map (stageToSpec D hRS q L (hq L))
  have hlr : ∀ L : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      formalSpectrumInclusion D (OrderDual.toDual L) ≫ r = 𝒴.map (kk L) :=
    fun L => formalSpectrumToSpec_spec D hRS q hq L
  -- The pullback of `Spec (R / (Ii + L))` over `Spec (R / Ii)` maps to `F` over the stage `L`.
  have hdex : ∀ L : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      ∃ d : 𝒴.obj (pullback i (kk L)) ⟶ F,
        d ≫ pullback.fst P Zc = 𝒴.map (pullback.snd i (kk L)) ≫
          formalSpectrumInclusion D (OrderDual.toDual L) ∧
        IsPullback (𝒴.map (pullback.snd i (kk L))) d
          (formalSpectrumInclusion D (OrderDual.toDual L)) (pullback.fst P Zc) := by
    intro L
    have hv := (IsPullback.of_hasPullback i (kk L)).map 𝒴
    let d : 𝒴.obj (pullback i (kk L)) ⟶ F :=
      hb.lift (𝒴.map (pullback.snd i (kk L)) ≫ formalSpectrumInclusion D (OrderDual.toDual L))
        (𝒴.map (pullback.fst i (kk L))) (by
          refine (Category.assoc _ _ _).trans ?_
          exact (congrArg (fun t => 𝒴.map (pullback.snd i (kk L)) ≫ t) (hlr L)).trans hv.w.symm)
    have hd₁ : d ≫ pullback.fst P Zc =
        𝒴.map (pullback.snd i (kk L)) ≫ formalSpectrumInclusion D (OrderDual.toDual L) :=
      hb.lift_fst _ _ _
    refine ⟨d, hd₁, IsPullback.of_bot (t := hb) (p := hd₁.symm) ?_⟩
    rw [hb.lift_snd _ _ _]
    exact hlr L ▸ hv.flip
  obtain ⟨d, -, hd⟩ := hdex K
  let V := pullback i (kk K)
  have hstage := formalSpectrumInclusion_isThickening' B S hS D (OrderDual.toDual K)
  have hdt : (MorphismProperty.relative 𝒴 (MorphismProperty.inverseImage
      (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u}) G)) d :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hd hstage
  -- `V` is affine, hence compact.
  have hiclosed : _root_.AlgebraicGeometry.IsClosedImmersion (G.map i) := by
    rw [heI]
    have _ : _root_.AlgebraicGeometry.IsClosedImmersion
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk Ii))) :=
      _root_.AlgebraicGeometry.IsClosedImmersion.spec_of_surjective _
        Ideal.Quotient.mk_surjective
    exact _root_.AlgebraicGeometry.IsClosedImmersion.comp eI.hom
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk Ii)))
  have _ : PreservesLimitsOfShape WalkingCospan G := by
    dsimp [G, BigFppfOver.toScheme, BigFppfOver.forget]
    infer_instance
  have _ : _root_.AlgebraicGeometry.IsClosedImmersion (G.map (pullback.snd i (kk K))) :=
    MorphismProperty.of_isPullback ((IsPullback.of_hasPullback i (kk K)).map G) hiclosed
  have _ : IsAffine (G.obj ((BigAffineFppf.inclusion B S hS).obj (D.stage K))) :=
    (D.stage K).property
  have hVaff : IsAffine (G.obj V) := isAffine_of_isAffineHom (G.map (pullback.snd i (kk K)))
  have hVcompact : CompactSpace (G.obj V) := by
    have _ := hVaff
    infer_instance
  -- A quasi-compact model of `F`, and the factorisation of `F ⟶ Spf R` through a stage.
  obtain ⟨F', hF'alg, hF'qc, ⟨eF⟩⟩ :=
    Space.exists_quasiCompact_model_of_relativeThickening hFalg V hVcompact d hdt
  have hDclosed : ∀ ⦃a₁ a₂ : OrderDual
      { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I }⦄ (f : a₁ ⟶ a₂),
      _root_.AlgebraicGeometry.IsClosedImmersion
        ((BigAffineFppf.toScheme B S hS).map (D.diagram.map f)) :=
    fun _ _ f => (quotientSystem_transition_isThickening' D (leOfHom f)).1
  obtain ⟨M, gM, hgM⟩ := exists_factor_through_thickening' B S hS _ D.diagram
    hDclosed (formalSpectrum D) (Iso.refl _) F' hF'qc (eF.hom ≫ pullback.fst P Zc)
  let tF : F ⟶ 𝒴.obj ((BigAffineFppf.inclusion B S hS).obj
      (D.stage (OrderDual.ofDual M))) := eF.inv ≫ gM
  have htF : tF ≫ formalSpectrumInclusion D M = pullback.fst P Zc := by
    have h₁ : gM ≫ formalSpectrumInclusion D M = eF.hom ≫ pullback.fst P Zc := by
      refine Eq.trans ?_ hgM
      exact congrArg (fun t => gM ≫ t) (Category.comp_id _).symm
    refine ((Category.assoc eF.inv gM (formalSpectrumInclusion D M)).trans ?_)
    exact (congrArg (fun t => eF.inv ≫ t) h₁).trans (eF.inv_hom_id_assoc _)
  -- Each quotient stage of `Spec (R / Ii)` maps to `Spec (R / M)` over `Spec R`.
  have _ : 𝒴.Full :=
    (Sheaf.fullyFaithfulSheafifiedYoneda (BigFppfOver.topology B S hS)).full
  have _ : 𝒴.Faithful :=
    (Sheaf.fullyFaithfulSheafifiedYoneda (BigFppfOver.topology B S hS)).faithful
  have key : ∀ L : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      ∃ f : Spec (.of (R ⧸ (Ii ⊔ L.1))) ⟶ Spec (.of (R ⧸ (OrderDual.ofDual M).1)),
        f ≫ Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.mk (OrderDual.ofDual M).1)) =
          Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ii ⊔ L.1))) := by
    intro L
    obtain ⟨dL, hdL, -⟩ := hdex L
    let vL : pullback i (kk L) ⟶
        (BigAffineFppf.inclusion B S hS).obj (D.stage (OrderDual.ofDual M)) :=
      𝒴.preimage (dL ≫ tF)
    let kM := (BigAffineFppf.inclusion B S hS).map
      (stageToSpec D hRS q (OrderDual.ofDual M) (hq (OrderDual.ofDual M)))
    have hlM : formalSpectrumInclusion D M ≫ r = 𝒴.map kM := hlr (OrderDual.ofDual M)
    have hvLM : vL ≫ kM = pullback.snd i (kk L) ≫ kk L := by
      apply 𝒴.map_injective
      rw [Functor.map_comp, Functor.map_comp, Functor.map_preimage,
        ← hlM, ← hlr L]
      calc (dL ≫ tF) ≫ formalSpectrumInclusion D M ≫ r
          = dL ≫ (tF ≫ formalSpectrumInclusion D M) ≫ r :=
            (Category.assoc _ _ _).trans (congrArg (fun t => dL ≫ t) (Category.assoc _ _ _).symm)
        _ = (dL ≫ pullback.fst P Zc) ≫ r :=
            (congrArg (fun t : F ⟶ formalSpectrum D => dL ≫ t ≫ r) htF).trans
              (Category.assoc _ _ _).symm
        _ = 𝒴.map (pullback.snd i (kk L)) ≫ formalSpectrumInclusion D (OrderDual.toDual L) ≫ r :=
            (congrArg (fun t => t ≫ r) hdL).trans (Category.assoc _ _ _)
    let qI : Spec (.of (R ⧸ (Ii ⊔ L.1))) ⟶ Spec (.of (R ⧸ Ii)) :=
      Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.factor (show Ii ≤ Ii ⊔ L.1 from le_sup_left)))
    let qL : Spec (.of (R ⧸ (Ii ⊔ L.1))) ⟶ Spec (.of (R ⧸ L.1)) :=
      Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.factor (show L.1 ≤ Ii ⊔ L.1 from le_sup_right)))
    have hqI : qI ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk Ii)) =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ii ⊔ L.1))) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
    have hqL : qL ≫ G.map (kk L) =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ii ⊔ L.1))) := by
      show qL ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk L.1)) = _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
    have hsL := (IsPullback.of_hasPullback i (kk L)).map G
    let jL : Spec (.of (R ⧸ (Ii ⊔ L.1))) ⟶ G.obj (pullback i (kk L)) :=
      hsL.lift (qI ≫ eI.inv) qL (by
        have h₁ : (qI ≫ eI.inv) ≫ G.map i =
            qI ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk Ii)) :=
          (Category.assoc qI eI.inv (G.map i)).trans
            ((congrArg (fun t => qI ≫ t) (congrArg (fun t => eI.inv ≫ t) heI)).trans
              (congrArg (fun t => qI ≫ t)
                (eI.inv_hom_id_assoc
                  (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk Ii))))))
        exact h₁.trans (hqI.trans hqL.symm))
    refine ⟨jL ≫ G.map vL, ?_⟩
    show (jL ≫ G.map vL) ≫ G.map kM = _
    rw [Category.assoc, ← G.map_comp, hvLM, G.map_comp, ← Category.assoc]
    exact (congrArg (fun t => t ≫ G.map (kk L)) (hsL.lift_snd _ _ _)).trans hqL
  -- Krull's intersection theorem.
  have hMI : (OrderDual.ofDual M).1 ≤ Ii :=
    ideal_le_of_quotientSpec_cofinal_factorizations
      (fun L : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I } => L.1) hD Ii _ key
  obtain ⟨n, hn⟩ := hD₁ (OrderDual.ofDual M)
  refine PrimeSpectrum.ext ?_
  exact @eq_maximalIdeal_of_pow_le_prime R _ hR.isLocal
    (Space.pointsToScheme B S hS U w).asIdeal
    (Space.pointsToScheme B S hS U w).isPrime n (hn.trans (hMI.trans hIP))

end AlgebraicGeometry.FormalSpace

end
