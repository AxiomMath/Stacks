module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AdicFibreCondition
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionAlongClosedSubsetReduction
public import StacksFrontier.AlgebraicGeometry.FormalSpace.MapsToAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValued
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence

/-!
# Adic maps out of a formal spectrum into a completion

Let `S` be a scheme, let `X` be an algebraic space over `S` and let `T ⊆ |X|` be a closed
subset whose complementary open subspace has quasi-compact inclusion `X \ T ⟶ X`. Let `R` be
a Noetherian complete local `S`-algebra with maximal ideal `𝔪`. **Stacks 0GBU** says that an
adic morphism

`p : Spf R ⟶ X_{/T}`

into the completion of `X` along `T` corresponds to a unique morphism `g : Spec R ⟶ X` whose
fibre over `T` is the closed point, `g⁻¹(T) = {𝔪}`; the correspondence sends `p` to the
algebraization of the composite `Spf R ⟶ X_{/T} ⟶ X`.

## Main definitions

* `AlgebraicGeometry.FormalSpace.completionToUpliftedSheaf`: the monomorphism
  `X_{/T} ⟶ X` from the completion of `X` along `T` into `X`, read in the sheaf of sets in
  which maps out of a formal spectrum live.
* `AlgebraicGeometry.FormalSpace.PreimageEqClosedPoint`: the condition `g⁻¹(T) = {𝔪}` on an
  `R`-point `g` of `X`, as an equality of subsets of the points of `Spec R`, and
  `AlgebraicGeometry.FormalSpace.PreimageSubsetClosedPoint`: its inclusion
  `g⁻¹(T) ⊆ {𝔪}`.

## Main results

* `AlgebraicGeometry.FormalSpace.pointsMap_mem_of_pointsToScheme_eq_closedPoint`: the closed
  point of `Spec R` lies over `T` for a morphism `Spec R ⟶ X` restricting on `Spf R` to a
  morphism into `X_{/T}`, which is the inclusion `{𝔪} ⊆ g⁻¹(T)`.
* `AlgebraicGeometry.FormalSpace.preimageSubsetClosedPoint_of_comp_eq`: the reverse inclusion
  `g⁻¹(T) ⊆ {𝔪}`.
* `AlgebraicGeometry.FormalSpace.existsUnique_algebraization_of_adic_into_completion`:
  **Stacks 0GBU**, the unique algebraization of an adic morphism into a completion.

## Implementation notes

*What carries the existence and the uniqueness.* Both are the bijectivity of restriction
along `Spf R ⟶ Spec R`, which is
`AlgebraicGeometry.FormalSpace.bijective_map_into_algebraicSpace` (**Stacks 0AQH**). Its
uniqueness half needs only the second cofinality condition on the weak ideals of definition,
that every power of `𝔪` contains one; its existence half needs both, so that the quotient
system presents the `𝔪`-adic formal spectrum.

*What carries the two inclusions of the fibre condition.* The inclusion `{𝔪} ⊆ g⁻¹(T)` is
`AlgebraicGeometry.FormalSpace.pointsMap_mem_of_pointsToScheme_eq_closedPoint`: the
restriction of `g` to a quotient stage `Spec (R / J)` factors through `X_{/T}`, so every point
of that stage has image in `T` by
`AlgebraicGeometry.Space.range_pointsMap_subset_of_whiskerRight_eq`, and for `J ⊆ 𝔪` the
closed point of `Spec R` is the image of a point of `Spec (R / J)`. The restriction to a stage
is read off through `AlgebraicGeometry.FormalSpace.formalSpectrumToSpec_spec` and Yoneda's
lemma for sheaves of sets.

The inclusion `g⁻¹(T) ⊆ {𝔪}` is
`AlgebraicGeometry.FormalSpace.pointsToScheme_eq_closedPoint_of_pointsMap_mem` of
`StacksFrontier.AlgebraicGeometry.FormalSpace.AdicFibreCondition`: it identifies
`Spf R ×_{X_{/T}} Z` with `Spf R ×_X Z` for `Z ⊆ X` the reduced induced closed subspace on
`T`, factors it through a quotient stage `Spec (R / M)`, and concludes `M ⊆ I` by Krull's
intersection theorem for the ideal `I` cutting out `Spec R ×_X Z`. It is the only place the
representability of `P` — which is what adicness of `P` supplies through **Stacks 0AQ3** — is
used. Quasi-compactness of `X \ T ⟶ X` is a hypothesis of the source, which uses it to see
that `X_{/T}` is adic*, so that adicness of `P` is meaningful at all; the proof here does not
appeal to it.

The fibre condition is stated through the comparison bijection
`AlgebraicGeometry.Space.pointsToScheme` of **Stacks 03BV** between the points of the
presheaf represented by `Spec R` in the site and the points of the scheme `Spec R`, so that
both sides of `g⁻¹(T) = {𝔪}` are subsets of the former.

## References

* [Stacks Project, Tag 0GBU](https://stacks.math.columbia.edu/tag/0GBU)
* [Stacks Project, Tag 0AQH](https://stacks.math.columbia.edu/tag/0AQH)
* [Stacks Project, Tag 0AQ3](https://stacks.math.columbia.edu/tag/0AQ3)
* [Stacks Project, Tag 0AQ1](https://stacks.math.columbia.edu/tag/0AQ1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FormalSpace

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The morphism `X_{/T} ⟶ X` from the completion of an algebraic space along a set of its
points into the algebraic space itself, with the target read as the sheaf of sets
`AlgebraicGeometry.FormalSpace.upliftedSheaf` in whose universe maps out of a formal spectrum
live. It is the inclusion of the completion subfunctor, lifted through the universal property
of sheafification, and it is a monomorphism by
`AlgebraicGeometry.Space.mono_completionSheafToAmbient`. -/
public def completionToUpliftedSheaf (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X) (T : Set (Space.points B S hS X)) :
    Space.completionSheaf B S hS X T ⟶ upliftedSheaf X hX :=
  ObjectProperty.homMk
    (Space.completionSheafToAmbient B S hS X (upliftedSheaf X hX).property T)

/-- The condition `g⁻¹(T) = {𝔪}` on an `R`-point `g` of a presheaf `X`, for `R` a Noetherian
complete local ring and `T` a set of points of `X`: the points of `Spec R` whose image in
`|X|` lies in `T` are exactly the closed point.

Both sides are subsets of the points of the presheaf represented by `Spec R` in the site; the
right-hand side is the preimage of the closed point under the comparison bijection
`AlgebraicGeometry.Space.pointsToScheme` of **Stacks 03BV**. -/
public def PreimageEqClosedPoint {R : Type u} [CommRing R]
    (hR : IsNoetherianCompleteLocalRing R)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (T : Set (Space.points B S hS X))
    (hRS : B.Contains (Spec (.of R))) (q : Spec (.of R) ⟶ S)
    (s : X.obj (op ((BigAffineFppf.inclusion B S hS).obj (specOver hRS q)))) : Prop :=
  Space.pointsMap B S hS
        (yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (specOver hRS q)))
        (yonedaEquiv.symm s) ⁻¹' T =
    Space.pointsToScheme B S hS ((BigAffineFppf.inclusion B S hS).obj (specOver hRS q)) ⁻¹'
      {@IsLocalRing.closedPoint R _ hR.isLocal}

/-- The condition `g⁻¹(T) ⊆ {𝔪}` on an `R`-point `g` of a presheaf `X`: every point of
`Spec R` whose image in `|X|` lies in `T` is the closed point. It is the half of
`AlgebraicGeometry.FormalSpace.PreimageEqClosedPoint` that Krull's intersection theorem
supplies in the source of **Stacks 0GBU**; the other half holds for the algebraization of any
morphism into the completion, by
`AlgebraicGeometry.FormalSpace.pointsMap_mem_of_pointsToScheme_eq_closedPoint`. -/
public def PreimageSubsetClosedPoint {R : Type u} [CommRing R]
    (hR : IsNoetherianCompleteLocalRing R)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (T : Set (Space.points B S hS X))
    (hRS : B.Contains (Spec (.of R))) (q : Spec (.of R) ⟶ S)
    (s : X.obj (op ((BigAffineFppf.inclusion B S hS).obj (specOver hRS q)))) : Prop :=
  Space.pointsMap B S hS
        (yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (specOver hRS q)))
        (yonedaEquiv.symm s) ⁻¹' T ⊆
    Space.pointsToScheme B S hS ((BigAffineFppf.inclusion B S hS).obj (specOver hRS q)) ⁻¹'
      {@IsLocalRing.closedPoint R _ hR.isLocal}

/-! ### The closed point lies over `T` -/

/-- Yoneda's lemma and its universe lift agree: the universe lift of the morphism of presheaves
named by a section is the morphism out of the universe-lifted representable named by the lifted
section. -/
private theorem whiskerRight_yonedaEquiv_symm {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {a : BigFppfOver B S hS} (t : X.obj (op a)) :
    Functor.whiskerRight (yonedaEquiv.symm t) uliftFunctor.{u + 1} =
      (uliftYonedaEquiv.{u + 1} (X := a) (F := X ⋙ uliftFunctor.{u + 1})).symm
        (ULift.up t) := by
  ext Y y
  rfl

/-- Transport a factorisation through a composite. Stated separately because at the point of
use the colimit presenting the formal spectrum carries two definitionally equal spellings of
the quotient stage, which a rewrite cannot see through. -/
private theorem comp_eq_comp_of_comp_eq {C : Type*} [Category C] {A A' A'' A''' : C}
    (u : A ⟶ A') (v : A' ⟶ A'') {w : A ⟶ A''} (hw : u ≫ v = w) {f : A'' ⟶ A'''}
    {z : A' ⟶ A'''} (h : v ≫ f = z) : w ≫ f = u ≫ z := by
  rw [← hw, Category.assoc, h]

/-- Every point of a quotient stage of `R` has image in `T` under an `R`-point of `X` that
restricts on `Spf R` to a morphism into the completion `X_{/T}`: the restriction of that point
to the stage factors through `X_{/T}`, so
`AlgebraicGeometry.Space.range_pointsMap_subset_of_whiskerRight_eq` applies. -/
private theorem range_pointsMap_stage_subset
    {R : Type u} [CommRing R] [TopologicalSpace R]
    (D : QuotientSystem B S hS R)
    (hRS : B.Contains (Spec (.of R))) (q : Spec (.of R) ⟶ S)
    (hq : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ q = D.overS J)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (T : Set (Space.points B S hS X))
    {P : formalSpectrum D ⟶ Space.completionSheaf B S hS X T}
    {g : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
        ((BigAffineFppf.inclusion B S hS).obj (specOver hRS q)) ⟶ upliftedSheaf X hX}
    (hg : formalSpectrumToSpec D hRS q hq ≫ g = P ≫ completionToUpliftedSheaf X hX T)
    (J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I }) :
    Set.range (Space.pointsMap B S hS
        (yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (D.stage J)))
        (yoneda.map ((BigAffineFppf.inclusion B S hS).map (stageToSpec D hRS q J (hq J))) ≫
          yonedaEquiv.symm
            (Sheaf.sectionEquiv (BigFppfOver.topology B S hS) g).down)) ⊆ T := by
  refine Space.range_pointsMap_subset_of_whiskerRight_eq B S hS T
    (upliftedSheaf X hX).property
    ((uliftYonedaEquiv.{u + 1}
        (X := (BigAffineFppf.inclusion B S hS).obj (D.stage J))
        (F := (Space.completionSheaf B S hS X T).obj)).symm
      (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)
        (formalSpectrumInclusion D (OrderDual.toDual J) ≫ P))) ?_
  have hα : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        ((BigAffineFppf.inclusion B S hS).map (stageToSpec D hRS q J (hq J))) ≫ g =
      (formalSpectrumInclusion D (OrderDual.toDual J) ≫ P) ≫
        completionToUpliftedSheaf X hX T :=
    (comp_eq_comp_of_comp_eq _ _ (formalSpectrumToSpec_spec D hRS q hq J) hg).trans
      (Category.assoc _ _ _).symm
  have hsec : Sheaf.sectionEquiv (BigFppfOver.topology B S hS)
        ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
          ((BigAffineFppf.inclusion B S hS).map (stageToSpec D hRS q J (hq J))) ≫ g) =
      ULift.up (X.map ((BigAffineFppf.inclusion B S hS).map
        (stageToSpec D hRS q J (hq J))).op
          (Sheaf.sectionEquiv (BigFppfOver.topology B S hS) g).down) :=
    Sheaf.sectionEquiv_map_comp (BigFppfOver.topology B S hS) _ g
  have hstep : Functor.whiskerRight
        (yoneda.map ((BigAffineFppf.inclusion B S hS).map
            (stageToSpec D hRS q J (hq J))) ≫
          yonedaEquiv.symm (Sheaf.sectionEquiv (BigFppfOver.topology B S hS) g).down)
        uliftFunctor.{u + 1} =
      (uliftYonedaEquiv.{u + 1}
          (X := (BigAffineFppf.inclusion B S hS).obj (D.stage J))
          (F := X ⋙ uliftFunctor.{u + 1})).symm
        (ULift.up (X.map ((BigAffineFppf.inclusion B S hS).map
          (stageToSpec D hRS q J (hq J))).op
            (Sheaf.sectionEquiv (BigFppfOver.topology B S hS) g).down)) := by
    rw [yonedaEquiv_symm_naturality_left]
    exact whiskerRight_yonedaEquiv_symm _
  rw [hstep, uliftYonedaEquiv_symm_comp]
  refine congrArg (uliftYonedaEquiv.{u + 1}
    (X := (BigAffineFppf.inclusion B S hS).obj (D.stage J))
    (F := X ⋙ uliftFunctor.{u + 1})).symm ?_
  rw [← hsec, hα]
  exact Sheaf.sectionEquiv_comp (BigFppfOver.topology B S hS) _
    (completionToUpliftedSheaf X hX T)

/-- The closed point of `Spec R` is the image of a point of the quotient stage of a weak ideal
of definition contained in the maximal ideal: that stage is `Spec (R / J)` with `J ⊆ 𝔪`, and
the image of `𝔪` is a prime ideal of `R / J` contracting to `𝔪`. -/
private theorem exists_pointsMap_pointsToScheme_eq_closedPoint
    {R : Type u} [CommRing R] [TopologicalSpace R] [IsLocalRing R]
    (D : QuotientSystem B S hS R)
    (hRS : B.Contains (Spec (.of R))) (q : Spec (.of R) ⟶ S)
    (J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I })
    (hJ : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ q = D.overS J)
    (hJm : J.1 ≤ IsLocalRing.maximalIdeal R) :
    ∃ y : Space.points B S hS
        (yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (D.stage J))),
      Space.pointsToScheme B S hS ((BigAffineFppf.inclusion B S hS).obj (specOver hRS q))
          (Space.pointsMap B S hS
            (yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (D.stage J)))
            (yoneda.map ((BigAffineFppf.inclusion B S hS).map
              (stageToSpec D hRS q J hJ))) y) =
        IsLocalRing.closedPoint R := by
  have hprime : (Ideal.map (Ideal.Quotient.mk J.1) (IsLocalRing.maximalIdeal R)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hJm)
  obtain ⟨y, hy⟩ := Space.surjective_pointsToScheme B S hS
    ((BigAffineFppf.inclusion B S hS).obj (D.stage J))
    (show (BigFppfOver.toScheme B S hS).obj
        ((BigAffineFppf.inclusion B S hS).obj (D.stage J)) from
      (⟨Ideal.map (Ideal.Quotient.mk J.1) (IsLocalRing.maximalIdeal R), hprime⟩ :
        PrimeSpectrum (R ⧸ J.1)))
  refine ⟨y, ?_⟩
  rw [Space.pointsToScheme_pointsMap_yoneda, hy]
  refine PrimeSpectrum.ext ?_
  have hker : Ideal.comap (Ideal.Quotient.mk J.1) (⊥ : Ideal (R ⧸ J.1)) = J.1 := Ideal.mk_ker
  change Ideal.comap (Ideal.Quotient.mk J.1)
      (Ideal.map (Ideal.Quotient.mk J.1) (IsLocalRing.maximalIdeal R)) =
    IsLocalRing.maximalIdeal R
  rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, hker]
  exact sup_eq_left.2 hJm

/-- **The closed point of `Spec R` lies over `T`.** Let `R` be a Noetherian complete local
`S`-algebra carrying a quotient system whose weak ideals of definition are cofinal among the
powers of the maximal ideal, and let `g : Spec R ⟶ X` restrict on `Spf R` to the composite of
a morphism `p : Spf R ⟶ X_{/T}` with `X_{/T} ⟶ X`. Then the closed point of `Spec R` has
image in `T` under `g`.

Indeed `g` restricted to a quotient stage `Spec (R / J)` factors through the completion, so
every point of that stage has image in `T`, and for `J ⊆ 𝔪` the closed point of `Spec R` is
the image of a point of `Spec (R / J)`. -/
public theorem pointsMap_mem_of_pointsToScheme_eq_closedPoint
    {R : Type u} [CommRing R] [TopologicalSpace R]
    (hR : IsNoetherianCompleteLocalRing R)
    (D : QuotientSystem B S hS R)
    (hD : ∀ n : ℕ, ∃ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      J.1 ≤ (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n)
    (hRS : B.Contains (Spec (.of R))) (q : Spec (.of R) ⟶ S)
    (hq : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ q = D.overS J)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (T : Set (Space.points B S hS X))
    {P : formalSpectrum D ⟶ Space.completionSheaf B S hS X T}
    {g : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
        ((BigAffineFppf.inclusion B S hS).obj (specOver hRS q)) ⟶ upliftedSheaf X hX}
    (hg : formalSpectrumToSpec D hRS q hq ≫ g = P ≫ completionToUpliftedSheaf X hX T)
    (w : Space.points B S hS
      (yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (specOver hRS q))))
    (hw : Space.pointsToScheme B S hS
        ((BigAffineFppf.inclusion B S hS).obj (specOver hRS q)) w =
      @IsLocalRing.closedPoint R _ hR.isLocal) :
    Space.pointsMap B S hS
        (yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (specOver hRS q)))
        (yonedaEquiv.symm (Sheaf.sectionEquiv (BigFppfOver.topology B S hS) g).down) w ∈ T := by
  have : IsLocalRing R := hR.isLocal
  obtain ⟨J, hJm⟩ := hD 1
  rw [pow_one] at hJm
  obtain ⟨y, hy⟩ :=
    exists_pointsMap_pointsToScheme_eq_closedPoint D hRS q J (hq J) hJm
  have hwy : w = Space.pointsMap B S hS
      (yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (D.stage J)))
      (yoneda.map ((BigAffineFppf.inclusion B S hS).map
        (stageToSpec D hRS q J (hq J)))) y :=
    Space.injective_pointsToScheme B S hS _ (hw.trans hy.symm)
  have hcomp : Space.pointsMap B S hS
        (yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (specOver hRS q)))
        (yonedaEquiv.symm (Sheaf.sectionEquiv (BigFppfOver.topology B S hS) g).down)
        (Space.pointsMap B S hS
          (yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (D.stage J)))
          (yoneda.map ((BigAffineFppf.inclusion B S hS).map
            (stageToSpec D hRS q J (hq J)))) y) =
      Space.pointsMap B S hS
        (yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (D.stage J)))
        (yoneda.map ((BigAffineFppf.inclusion B S hS).map
            (stageToSpec D hRS q J (hq J))) ≫
          yonedaEquiv.symm (Sheaf.sectionEquiv (BigFppfOver.topology B S hS) g).down) y := by
    rw [Space.pointsMap_comp]
    rfl
  rw [hwy, hcomp]
  exact range_pointsMap_stage_subset D hRS q hq hX T hg J ⟨y, rfl⟩

/-- **The fibre of an algebraization over `T` is contained in the closed point.** Let `R` be a
Noetherian complete local `S`-algebra carrying a quotient system whose weak ideals of
definition are cofinal among the powers of the maximal ideal, let `T` be a closed set of points
of an algebraic space `X` over `S`, and let `g : Spec R ⟶ X` restrict on `Spf R` to the
composite of a morphism `p : Spf R ⟶ X_{/T}` representable by algebraic spaces with
`X_{/T} ⟶ X`. Then `g⁻¹(T) ⊆ {𝔪}`. -/
public theorem preimageSubsetClosedPoint_of_comp_eq
    {R : Type u} [CommRing R] [TopologicalSpace R]
    (hR : IsNoetherianCompleteLocalRing R)
    (D : QuotientSystem B S hS R)
    (hD₁ : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      ∃ n : ℕ, (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n ≤ J.1)
    (hD : ∀ n : ℕ, ∃ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      J.1 ≤ (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n)
    (hRS : B.Contains (Spec (.of R))) (q : Spec (.of R) ⟶ S)
    (hq : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ q = D.overS J)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (T : Set (Space.points B S hS X))
    (hT : @IsClosed _ (Space.pointTopology B S hS X) T)
    {P : formalSpectrum D ⟶ Space.completionSheaf B S hS X T}
    (hPadic : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS P.hom)
    {g : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
        ((BigAffineFppf.inclusion B S hS).obj (specOver hRS q)) ⟶ upliftedSheaf X hX}
    (hg : formalSpectrumToSpec D hRS q hq ≫ g = P ≫ completionToUpliftedSheaf X hX T) :
    PreimageSubsetClosedPoint hR T hRS q
      (Sheaf.sectionEquiv (BigFppfOver.topology B S hS) g).down := fun v hv =>
  pointsToScheme_eq_closedPoint_of_pointsMap_mem hR D hD₁ hD hRS q hq hX T hT hPadic hg v hv

/-- **Stacks 0GBU.** Let `S` be a scheme, `X` an algebraic space over `S` and `T` a closed
set of points of `X` whose complementary open subspace has quasi-compact inclusion into `X`.
Let `R` be a Noetherian complete local `S`-algebra whose spectrum lies in the site, equipped
with a quotient system whose weak ideals of definition are cofinal among the powers of the
maximal ideal. Then an adic morphism `p : Spf R ⟶ X_{/T}` into the completion of `X` along
`T` admits a unique algebraization: a unique morphism `g : Spec R ⟶ X` restricting on
`Spf R` to the composite `Spf R ⟶ X_{/T} ⟶ X` and satisfying `g⁻¹(T) = {𝔪}`.

The existence and uniqueness of the algebraization are the two halves of **Stacks 0AQH**,
`AlgebraicGeometry.FormalSpace.bijective_map_into_algebraicSpace`. The inclusion
`{𝔪} ⊆ g⁻¹(T)` of the fibre condition is
`AlgebraicGeometry.FormalSpace.pointsMap_mem_of_pointsToScheme_eq_closedPoint` and the reverse
inclusion `g⁻¹(T) ⊆ {𝔪}` is
`AlgebraicGeometry.FormalSpace.preimageSubsetClosedPoint_of_comp_eq`. -/
@[stacks 0GBU "The algebraization, its existence and uniqueness, and both inclusions of its \
fibre condition g⁻¹(T) = {𝔪}, the second of them by Krull's intersection theorem."]
public theorem existsUnique_algebraization_of_adic_into_completion
    {R : Type u} [CommRing R] [TopologicalSpace R]
    (hR : IsNoetherianCompleteLocalRing R)
    (D : QuotientSystem B S hS R)
    (hD₁ : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      ∃ n : ℕ, (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n ≤ J.1)
    (hD : ∀ n : ℕ, ∃ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      J.1 ≤ (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n)
    (hRS : B.Contains (Spec (.of R))) (q : Spec (.of R) ⟶ S)
    (hq : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ q = D.overS J)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (T : Set (Space.points B S hS X))
    (hT : @IsClosed _ (Space.pointTopology B S hS X) T)
    (_hTqc : letI : TopologicalSpace (Space.points B S hS X) := Space.pointTopology B S hS X
      Space.IsQuasiCompact B S hS
        ((Space.openSubspacesOrderIso B S hS X hX).symm ⟨Tᶜ, hT.isOpen_compl⟩).1.ι)
    (P : formalSpectrum D ⟶ Space.completionSheaf B S hS X T)
    (hPadic : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS P.hom) :
    ∃! g : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
        ((BigAffineFppf.inclusion B S hS).obj (specOver hRS q)) ⟶ upliftedSheaf X hX,
      formalSpectrumToSpec D hRS q hq ≫ g = P ≫ completionToUpliftedSheaf X hX T ∧
        PreimageEqClosedPoint hR T hRS q
          (Sheaf.sectionEquiv (BigFppfOver.topology B S hS) g).down := by
  obtain ⟨g, hg⟩ := surjective_map_into_algebraicSpace hR D hD₁ hD hRS q hq X hX
    (P ≫ completionToUpliftedSheaf X hX T)
  refine ⟨g, ⟨hg, Set.Subset.antisymm
    (preimageSubsetClosedPoint_of_comp_eq hR D hD₁ hD hRS q hq hX T hT hPadic hg)
    fun w hw => ?_⟩, fun g' hg' =>
    injective_map_into_algebraicSpace hR D hD hRS q hq X hX (hg'.1.trans hg.symm)⟩
  exact pointsMap_mem_of_pointsToScheme_eq_closedPoint hR D hD hRS q hq hX T hg w hw

end AlgebraicGeometry.FormalSpace

end
