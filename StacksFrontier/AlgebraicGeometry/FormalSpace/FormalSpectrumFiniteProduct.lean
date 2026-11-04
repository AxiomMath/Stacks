module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrumRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Surjective
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteCoproduct
public import StacksFrontier.RingTheory.Ideal.FiniteProductQuotient
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletionOverPi
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdicProduct

/-!
# The formal spectrum of a finite product of topological rings

Let `S` be a scheme contained in a big fppf site `B` and let `A i` be finitely many
topological rings carrying quotient systems over `S`. This file equips the product `∀ i, A i`
with a quotient system over `S` and identifies the maps out of its formal spectrum, so that a
jointly surjective finite family of formal spectra over a base can be read as the surjectivity
of a *single* formal spectrum map — which is the shape in which condition (1) of
**Stacks 0AN9** (`AlgebraicGeometry.FormalSpace.etaleFormalSpectrumMap_surjective_tfae`)
accepts it.

The weak ideals of definition of `∀ i, A i` are exactly the products of weak ideals of
definition of the factors: a product of open ideals of topologically nilpotent elements is one,
and conversely the coordinate image of a weak ideal of definition is one, because `Pi.single`
carries an element of the image back into the ideal. Consequently the quotient of the product
by a weak ideal of definition is the product of the quotients of the factors by its coordinate
ideals (`Ideal.quotientPiEvalRingEquiv`), and its spectrum is therefore the *coproduct* of the
quotient spectra of the factors — Mathlib's `AlgebraicGeometry.sigmaSpec`, an isomorphism for a
finite index. That coproduct description supplies both halves of the quotient-system datum: the
spectrum lies in the site because a finite coproduct of schemes of the site does, and its
structure morphism to `S` is the one descended from the structure morphisms of the factors.

## Main results

* `TopologicalRing.isWeakIdealOfDefinition_pi` and
  `TopologicalRing.isWeakIdealOfDefinition_map_evalRingHom_of_isTopologicalRing`: the weak
  ideals of definition of a finite product, in both directions; the second for any index set
  and any topological rings, where
  `TopologicalRing.isWeakIdealOfDefinition_map_evalRingHom` asks for a finite product of
  weakly admissible linearly topologized rings.
* `AlgebraicGeometry.FormalSpace.isColimitPiStageCofan`: the quotient spectrum of a finite
  product by a weak ideal of definition is the coproduct of the quotient spectra of the factors
  by the coordinate ideals.
* `AlgebraicGeometry.FormalSpace.quotientSystemPi`: the quotient system of a finite product.
* `AlgebraicGeometry.FormalSpace.continuousHomPiProjection` and
  `AlgebraicGeometry.FormalSpace.continuousHomPi`: the coordinate projections out of it and the
  product of finitely many continuous homomorphisms into it.
* `AlgebraicGeometry.FormalSpace.isSurjective_of_isLocallySurjective_sigmaDesc_of_factors`: a
  morphism through which a jointly surjective family factors is surjective on points.
* `AlgebraicGeometry.FormalSpace.isSurjective_formalSpectrumMap_continuousHomPi`: a jointly
  surjective finite family of formal spectra over a base makes the formal spectrum map of the
  product of the presenting homomorphisms surjective.

## Implementation notes

The full statement that `Spf` of a finite product *is* the coproduct of the `Spf`s of the
factors is not proved here and is not needed for the surjectivity above: the coproduct
description is used one quotient stage at a time, where it is Mathlib's `sigmaSpec`, and the
passage from a jointly surjective family to surjectivity of a single map only needs the family
to *factor* through that map. The factorisation is `formalSpectrumMap` of the coordinate
projections, and `AlgebraicGeometry.FormalSpace.IsSurjective` is surjectivity on points, which
a factorisation transports because
`AlgebraicGeometry.FormalSpace.exists_pointsMapULift_eq_of_isLocallySurjective_sigmaDesc`
makes a sheaf-surjective coproduct morphism into a jointly surjective family on points.

No statement here carries a `@[stacks]` registration: they are the finite-product bookkeeping
around the construction of Stacks 0AIF, not numbered statements of the source.

## References

* [Stacks Project, Tag 0AIF](https://stacks.math.columbia.edu/tag/0AIF)
* [Stacks Project, Tag 0AMV](https://stacks.math.columbia.edu/tag/0AMV)
* [Stacks Project, Tag 0AN9](https://stacks.math.columbia.edu/tag/0AN9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace TopologicalRing

universe u v w

section WeakIdeals

variable {ι : Type w} {A : ι → Type v} [∀ i, CommRing (A i)] [∀ i, TopologicalSpace (A i)]

/-- A product of weak ideals of definition is a weak ideal of definition of the finite
product: a product of open ideals is open, and an element of the product is topologically
nilpotent as soon as each of its coordinates is. -/
public theorem isWeakIdealOfDefinition_pi [Finite ι] [∀ i, IsTopologicalRing (A i)]
    {J : ∀ i, Ideal (A i)} (hJ : ∀ i, IsWeakIdealOfDefinition (J i)) :
    IsWeakIdealOfDefinition (Ideal.pi J) := by
  have hset : (Ideal.pi J : Set (∀ i, A i)) = Set.pi Set.univ fun i ↦ (J i : Set (A i)) := by
    ext x
    simp [Ideal.mem_pi]
  refine ⟨?_, ?_⟩
  · rw [hset]
    exact isOpen_pi_iff'.2 fun x hx ↦ ⟨fun i ↦ (J i : Set (A i)), fun i ↦
      ⟨(hJ i).1, hx i (Set.mem_univ i)⟩, fun y hy i _ ↦ hy i (Set.mem_univ i)⟩
  · intro x hx
    rw [IsTopologicallyNilpotent, tendsto_pi_nhds]
    intro i
    simp only [Pi.pow_apply]
    exact (hJ i).2 (x i) (hx i)

/-- The image of a weak ideal of definition of a product under a coordinate projection is a
weak ideal of definition: the projection is an open continuous ring map with a section through
`Pi.single`, so openness and topological nilpotence both transfer. -/
public theorem isWeakIdealOfDefinition_map_evalRingHom_of_isTopologicalRing
    [∀ i, IsTopologicalRing (A i)] {K : Ideal (∀ i, A i)}
    (hK : IsWeakIdealOfDefinition K) (i : ι) :
    IsWeakIdealOfDefinition (K.map (Pi.evalRingHom A i)) := by
  classical
  have hsingle {x : A i} (hx : x ∈ K.map (Pi.evalRingHom A i)) :
      (Pi.single i x : ∀ j, A j) ∈ K := by
    obtain ⟨y, hy, hxy⟩ := (Ideal.mem_map_iff_of_surjective (Pi.evalRingHom A i)
      (Function.surjective_eval i)).mp hx
    have heq : (Pi.single i x : ∀ j, A j) = (Pi.single i 1 : ∀ j, A j) * y := by
      funext j
      obtain rfl | hij := eq_or_ne i j
      · simpa using hxy.symm
      · simp [Pi.single_eq_of_ne (Ne.symm hij)]
    rw [heq]
    exact K.mul_mem_left _ hy
  obtain ⟨t, w, hw, hsub⟩ := isOpen_pi_iff.mp hK.1 0 (SetLike.mem_coe.mpr K.zero_mem)
  have hmem {x : A i} (hx : i ∈ t → x ∈ w i) : x ∈ K.map (Pi.evalRingHom A i) := by
    have hin : (Pi.single i x : ∀ j, A j) ∈ (t : Set ι).pi w := by
      intro j hj
      obtain rfl | hij := eq_or_ne i j
      · simpa using hx hj
      · simpa [Pi.single_eq_of_ne (Ne.symm hij)] using (hw j hj).2
    simpa using Ideal.mem_map_of_mem (Pi.evalRingHom A i) (hsub hin)
  refine ⟨?_, ?_⟩
  · by_cases hi : i ∈ t
    · exact (K.map (Pi.evalRingHom A i)).toAddSubgroup.isOpen_of_mem_nhds
        (Filter.mem_of_superset ((hw i hi).1.mem_nhds (hw i hi).2)
          fun x hx ↦ hmem fun _ ↦ hx)
    · have htop : K.map (Pi.evalRingHom A i) = ⊤ :=
        Ideal.eq_top_iff_one _ |>.mpr (hmem fun h ↦ absurd h hi)
      rw [htop]
      simp
  · intro x hx
    have hcont : Continuous (Pi.evalRingHom A i) := continuous_apply i
    simpa using (hK.2 _ (hsingle hx)).map hcont

end WeakIdeals

end TopologicalRing

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] sheaf_hasColimits

/-- **A morphism through which a jointly surjective family factors is surjective.** If the
morphism out of the coproduct of a family `{Yᵢ ⟶ Y}` of morphisms of fppf sheaves is a
surjection of sheaves and each member factors through `q : Z ⟶ Y`, then `q` is surjective on
points: a point of `Y` is the image of a point of some `Yᵢ`, whose image in `Z` is a preimage
of it. -/
theorem isSurjective_of_isLocallySurjective_sigmaDesc_of_factors {I : Type (u + 1)}
    {Yi : I → FppfSheaf B S hS} {Z Y : FppfSheaf B S hS} (c : ∀ i, Yi i ⟶ Y)
    (hc : Sheaf.IsLocallySurjective (Sigma.desc c)) {q : Z ⟶ Y} (p : ∀ i, Yi i ⟶ Z)
    (hp : ∀ i, p i ≫ q = c i) :
    IsSurjective B S hS q := by
  intro y
  obtain ⟨i, z, hz⟩ :=
    exists_pointsMapULift_eq_of_isLocallySurjective_sigmaDesc B S hS c hc y
  refine ⟨Space.pointsMapULift.{u + 1} B S hS (Yi i).obj (p i).hom z, ?_⟩
  have hcomp : (p i).hom ≫ q.hom = (c i).hom := congrArg (fun f ↦ f.hom) (hp i)
  rw [← hz, ← hcomp, Space.pointsMapULift_comp, Function.comp_apply]

/-! ### The quotient system of a finite product -/

section FiniteProduct

variable {ι : Type u} [Finite ι] {A : ι → Type u} [∀ i, CommRing (A i)]
  [∀ i, TopologicalSpace (A i)] [∀ i, IsTopologicalRing (A i)]

/-- The `i`-th coordinate of a weak ideal of definition of a finite product of topological
rings, a weak ideal of definition of the `i`-th factor. -/
def piCoordIdeal
    (J : { I : Ideal (∀ i, A i) // TopologicalRing.IsWeakIdealOfDefinition I }) (i : ι) :
    { I : Ideal (A i) // TopologicalRing.IsWeakIdealOfDefinition I } :=
  ⟨J.1.map (Pi.evalRingHom A i),
    TopologicalRing.isWeakIdealOfDefinition_map_evalRingHom_of_isTopologicalRing J.2 i⟩

/-- The `i`-th summand inclusion of the quotient spectrum of a finite product by a weak ideal
of definition: the spectrum of the quotient of the `i`-th factor by the `i`-th coordinate
ideal, included along the `i`-th projection. -/
def piStageIncl
    (J : { I : Ideal (∀ i, A i) // TopologicalRing.IsWeakIdealOfDefinition I }) (i : ι) :
    Spec (.of (A i ⧸ (piCoordIdeal J i).1)) ⟶ Spec (.of ((∀ j, A j) ⧸ J.1)) :=
  Spec.map (CommRingCat.ofHom (Ideal.quotientMap (piCoordIdeal J i).1 (Pi.evalRingHom A i)
    Ideal.le_comap_map))

omit [Finite ι] in
/-- A quotient of a finite product of rings by a weak ideal of definition, compared with the
quotients of the factors by its coordinate ideals: the comparison on the `i`-th summand is the
quotient map induced by the `i`-th projection. -/
theorem quotientMap_evalRingHom_comp_factor
    (J L : { I : Ideal (∀ i, A i) // TopologicalRing.IsWeakIdealOfDefinition I })
    (h : (J.1 : Ideal (∀ i, A i)) ≤ L.1) (i : ι) :
    (Ideal.quotientMap (piCoordIdeal L i).1 (Pi.evalRingHom A i) Ideal.le_comap_map).comp
        (Ideal.Quotient.factor h) =
      (Ideal.Quotient.factor (Ideal.map_mono h : (piCoordIdeal J i).1 ≤ (piCoordIdeal L i).1)).comp
        (Ideal.quotientMap (piCoordIdeal J i).1 (Pi.evalRingHom A i) Ideal.le_comap_map) :=
  Ideal.Quotient.ringHom_ext (RingHom.ext fun _ ↦ rfl)

/-- **The quotient spectrum of a finite product is the coproduct of the quotient spectra of
its factors.** The quotient of a finite product of rings by a weak ideal of definition is the
product of the quotients of the factors by its coordinate ideals, and the spectrum of a finite
product of rings is the coproduct of the spectra. -/
noncomputable def isColimitPiStageCofan
    (J : { I : Ideal (∀ i, A i) // TopologicalRing.IsWeakIdealOfDefinition I }) :
    IsColimit (Cofan.mk (Spec (.of ((∀ j, A j) ⧸ J.1))) (piStageIncl J)) := by
  let Rq : ι → CommRingCat.{u} := fun i ↦ CommRingCat.of (A i ⧸ (piCoordIdeal J i).1)
  have hsigma : IsColimit (Cofan.mk (Spec (.of (∀ i, A i ⧸ (piCoordIdeal J i).1)))
      (fun i ↦ Spec.map (CommRingCat.ofHom
        (Pi.evalRingHom (fun j ↦ A j ⧸ (piCoordIdeal J j).1) i)))) :=
    Cofan.isColimitOfIso (coproductIsCoproduct fun i ↦ Spec (Rq i))
      (asIso (sigmaSpec Rq)) fun i ↦ ι_sigmaSpec Rq i
  refine Cofan.isColimitOfIso hsigma
    (Scheme.Spec.mapIso (Ideal.quotientPiEvalRingEquiv J.1).toCommRingCatIso.op) fun i ↦ ?_
  have hcr : (Ideal.quotientPiEvalRingEquiv J.1).toCommRingCatIso.hom ≫
        CommRingCat.ofHom (Pi.evalRingHom (fun j ↦ A j ⧸ (piCoordIdeal J j).1) i) =
      CommRingCat.ofHom (Ideal.quotientMap (piCoordIdeal J i).1 (Pi.evalRingHom A i)
        Ideal.le_comap_map) :=
    CommRingCat.hom_ext (Ideal.evalRingHom_comp_quotientPiEvalRingEquiv J.1 i)
  calc Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun j ↦ A j ⧸ (piCoordIdeal J j).1) i)) ≫
        Spec.map (Ideal.quotientPiEvalRingEquiv J.1).toCommRingCatIso.hom
      = Spec.map ((Ideal.quotientPiEvalRingEquiv J.1).toCommRingCatIso.hom ≫
          CommRingCat.ofHom (Pi.evalRingHom (fun j ↦ A j ⧸ (piCoordIdeal J j).1) i)) :=
        (Spec.map_comp _ _).symm
    _ = piStageIncl J i := congrArg (fun f ↦ Spec.map f) hcr

/-- The spectrum of a quotient of a finite product by a weak ideal of definition lies in the
site: it is the coproduct of the quotient spectra of the factors, which lie in the site. -/
theorem contains_spec_quotient_pi (E : ∀ i, QuotientSystem B S hS (A i))
    (J : { I : Ideal (∀ i, A i) // TopologicalRing.IsWeakIdealOfDefinition I }) :
    B.Contains (Spec (.of ((∀ j, A j) ⧸ J.1))) := by
  have hc : B.Contains (∐ fun i ↦ Spec (CommRingCat.of (A i ⧸ (piCoordIdeal J i).1))) :=
    B.contains_sigma _ fun i ↦ (E i).inSite (piCoordIdeal J i)
  have e : (∐ fun i ↦ Spec (CommRingCat.of (A i ⧸ (piCoordIdeal J i).1))) ≅
      Spec (.of ((∀ j, A j) ⧸ J.1)) :=
    IsColimit.coconePointUniqueUpToIso
      (coproductIsCoproduct fun i ↦ Spec (CommRingCat.of (A i ⧸ (piCoordIdeal J i).1)))
      (isColimitPiStageCofan J)
  have hsize : (∐ fun i ↦ Spec (CommRingCat.of (A i ⧸ (piCoordIdeal J i).1))).size <
    B.cutoff := hc
  rwa [Scheme.size_congr e] at hsize

/-- The structure morphism to `S` of a quotient of a finite product by a weak ideal of
definition: the one descended from the structure morphisms of the quotients of the factors by
the coordinate ideals. -/
noncomputable def piOverS (E : ∀ i, QuotientSystem B S hS (A i))
    (J : { I : Ideal (∀ i, A i) // TopologicalRing.IsWeakIdealOfDefinition I }) :
    Spec (.of ((∀ j, A j) ⧸ J.1)) ⟶ S :=
  Cofan.IsColimit.desc (isColimitPiStageCofan J) fun i ↦ (E i).overS (piCoordIdeal J i)

/-- The structure morphism `piOverS` restricted to the `i`-th summand is the structure morphism of
the quotient of the `i`-th factor by the coordinate ideal. -/
theorem piStageIncl_comp_piOverS (E : ∀ i, QuotientSystem B S hS (A i))
    (J : { I : Ideal (∀ i, A i) // TopologicalRing.IsWeakIdealOfDefinition I }) (i : ι) :
    piStageIncl J i ≫ piOverS B S hS E J = (E i).overS (piCoordIdeal J i) :=
  Cofan.IsColimit.fac (isColimitPiStageCofan J) _ i

/-- Two morphisms out of a quotient of a finite product by a weak ideal of definition agree as
soon as they agree on every summand. -/
theorem piStage_hom_ext
    {J : { I : Ideal (∀ i, A i) // TopologicalRing.IsWeakIdealOfDefinition I }} {T : Scheme.{u}}
    {m n : Spec (.of ((∀ j, A j) ⧸ J.1)) ⟶ T}
    (hmn : ∀ i, piStageIncl J i ≫ m = piStageIncl J i ≫ n) : m = n :=
  Cofan.IsColimit.hom_ext (isColimitPiStageCofan J) m n hmn

/-- **The quotient system of a finite product.** Quotient systems over `S` for finitely many
topological rings induce one for their product: the quotient of the product by a weak ideal of
definition is the product of the quotients of the factors by its coordinate ideals, so its
spectrum is the coproduct of the given quotient spectra, which lies in the site and carries the
morphism to `S` descended from theirs. -/
noncomputable def quotientSystemPi (E : ∀ i, QuotientSystem B S hS (A i)) :
    QuotientSystem B S hS (∀ i, A i) where
  inSite J := contains_spec_quotient_pi B S hS E J
  overS J := piOverS B S hS E J
  compatible J L h := by
    refine piStage_hom_ext fun i ↦ ?_
    have hk : (piCoordIdeal J i).1 ≤ (piCoordIdeal L i).1 := Ideal.map_mono h
    have hcr : CommRingCat.ofHom (Ideal.Quotient.factor h) ≫
          CommRingCat.ofHom (Ideal.quotientMap (piCoordIdeal L i).1 (Pi.evalRingHom A i)
            Ideal.le_comap_map) =
        CommRingCat.ofHom (Ideal.quotientMap (piCoordIdeal J i).1 (Pi.evalRingHom A i)
            Ideal.le_comap_map) ≫ CommRingCat.ofHom (Ideal.Quotient.factor hk) :=
      CommRingCat.hom_ext (quotientMap_evalRingHom_comp_factor J L h i)
    have hfac : piStageIncl L i ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h)) =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hk)) ≫ piStageIncl J i :=
      (Spec.map_comp _ _).symm.trans ((congrArg (fun f ↦ Spec.map f) hcr).trans
        (Spec.map_comp _ _))
    change piStageIncl L i ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h)) ≫
        piOverS B S hS E J = piStageIncl L i ≫ piOverS B S hS E L
    rw [← Category.assoc, hfac, Category.assoc, piStageIncl_comp_piOverS,
      piStageIncl_comp_piOverS]
    exact (E i).compatible (piCoordIdeal J i) (piCoordIdeal L i) hk

/-- The structure morphism of the quotient system of a finite product is `piOverS`. -/
@[simp]
theorem overS_quotientSystemPi (E : ∀ i, QuotientSystem B S hS (A i))
    (J : { I : Ideal (∀ i, A i) // TopologicalRing.IsWeakIdealOfDefinition I }) :
    (quotientSystemPi B S hS E).overS J = piOverS B S hS E J := rfl

/-- **The `i`-th projection as a continuous homomorphism over `S`** out of the quotient system
of a finite product. -/
def continuousHomPiProjection (E : ∀ i, QuotientSystem B S hS (A i)) (i : ι) :
    ContinuousHom (quotientSystemPi B S hS E) (E i) where
  toRingHom := Pi.evalRingHom A i
  continuous := continuous_apply i
  overS J K h := by
    have hle : (piCoordIdeal J i).1 ≤ K.1 := Ideal.map_le_iff_le_comap.mpr h
    have hring : Ideal.quotientMap K.1 (Pi.evalRingHom A i) h =
        (Ideal.Quotient.factor hle).comp
          (Ideal.quotientMap (piCoordIdeal J i).1 (Pi.evalRingHom A i) Ideal.le_comap_map) :=
      Ideal.Quotient.ringHom_ext (RingHom.ext fun _ ↦ rfl)
    have hcr : CommRingCat.ofHom (Ideal.quotientMap K.1 (Pi.evalRingHom A i) h) =
        CommRingCat.ofHom (Ideal.quotientMap (piCoordIdeal J i).1 (Pi.evalRingHom A i)
            Ideal.le_comap_map) ≫
          CommRingCat.ofHom (Ideal.Quotient.factor hle) :=
      CommRingCat.hom_ext hring
    have h2 : Spec.map (CommRingCat.ofHom (Ideal.quotientMap K.1 (Pi.evalRingHom A i) h)) =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hle)) ≫ piStageIncl J i :=
      (congrArg (fun f ↦ Spec.map f) hcr).trans (Spec.map_comp _ _)
    rw [overS_quotientSystemPi, h2, Category.assoc, piStageIncl_comp_piOverS]
    exact (E i).compatible (piCoordIdeal J i) K hle

/-- The ring homomorphism underlying the `i`-th projection is evaluation at `i`. -/
@[simp]
theorem continuousHomPiProjection_toRingHom (E : ∀ i, QuotientSystem B S hS (A i)) (i : ι) :
    (continuousHomPiProjection B S hS E i).toRingHom = Pi.evalRingHom A i := rfl

/-- **The product of finitely many continuous homomorphisms over `S`** into the quotient system
of a finite product. -/
def continuousHomPi {R : Type u} [CommRing R] [TopologicalSpace R]
    {D : QuotientSystem B S hS R} (E : ∀ i, QuotientSystem B S hS (A i))
    (ψ : ∀ i, ContinuousHom D (E i)) :
    ContinuousHom D (quotientSystemPi B S hS E) where
  toRingHom := RingHom.pi fun i ↦ (ψ i).toRingHom
  continuous := continuous_pi fun i ↦ (ψ i).continuous
  overS J K h := by
    refine piStage_hom_ext fun i ↦ ?_
    have hle : (J.1 : Ideal R) ≤ Ideal.comap (ψ i).toRingHom (piCoordIdeal K i).1 := by
      intro r hr
      have hmem : (RingHom.pi fun j ↦ (ψ j).toRingHom) r ∈ K.1 := h hr
      exact Ideal.mem_map_of_mem (Pi.evalRingHom A i) hmem
    have hring : (Ideal.quotientMap (piCoordIdeal K i).1 (Pi.evalRingHom A i)
          Ideal.le_comap_map).comp
          (Ideal.quotientMap K.1 (RingHom.pi fun j ↦ (ψ j).toRingHom) h) =
        Ideal.quotientMap (piCoordIdeal K i).1 (ψ i).toRingHom hle :=
      Ideal.Quotient.ringHom_ext (RingHom.ext fun _ ↦ rfl)
    have hcr : CommRingCat.ofHom (Ideal.quotientMap K.1
            (RingHom.pi fun j ↦ (ψ j).toRingHom) h) ≫
          CommRingCat.ofHom (Ideal.quotientMap (piCoordIdeal K i).1 (Pi.evalRingHom A i)
            Ideal.le_comap_map) =
        CommRingCat.ofHom (Ideal.quotientMap (piCoordIdeal K i).1 (ψ i).toRingHom hle) :=
      CommRingCat.hom_ext hring
    have h2 : piStageIncl K i ≫ Spec.map (CommRingCat.ofHom (Ideal.quotientMap K.1
            (RingHom.pi fun j ↦ (ψ j).toRingHom) h)) =
        Spec.map (CommRingCat.ofHom (Ideal.quotientMap (piCoordIdeal K i).1
          (ψ i).toRingHom hle)) :=
      (Spec.map_comp _ _).symm.trans (congrArg (fun f ↦ Spec.map f) hcr)
    rw [← Category.assoc, h2, (ψ i).overS J (piCoordIdeal K i) hle, overS_quotientSystemPi,
      piStageIncl_comp_piOverS]

/-- The ring homomorphism underlying a product of continuous homomorphisms is the product of their
ring homomorphisms. -/
@[simp]
theorem continuousHomPi_toRingHom {R : Type u} [CommRing R] [TopologicalSpace R]
    {D : QuotientSystem B S hS R} (E : ∀ i, QuotientSystem B S hS (A i))
    (ψ : ∀ i, ContinuousHom D (E i)) :
    (continuousHomPi B S hS E ψ).toRingHom = RingHom.pi fun i ↦ (ψ i).toRingHom := rfl

/-! ### Surjectivity of the formal spectrum of a finite product -/

section Surjectivity

variable [∀ i, IsLinearTopology (A i) (A i)] [IsLinearTopology (∀ i, A i) (∀ i, A i)]
  {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R]

omit [∀ (i : ι), IsLinearTopology (A i) (A i)] in
/-- The formal spectrum of the `i`-th projection, followed by the formal spectrum of a product
of continuous homomorphisms, is the formal spectrum of the `i`-th factor. -/
theorem formalSpectrumMap_continuousHomPiProjection_comp
    (hprod : TopologicalRing.IsWeaklyAdmissible (∀ i, A i))
    (hR : TopologicalRing.IsWeaklyAdmissible R) {D : QuotientSystem B S hS R}
    (E : ∀ i, QuotientSystem B S hS (A i)) (ψ : ∀ i, ContinuousHom D (E i)) (i : ι) :
    formalSpectrumMap hprod (continuousHomPiProjection B S hS E i) ≫
        formalSpectrumMap hR (continuousHomPi B S hS E ψ) =
      formalSpectrumMap hR (ψ i) :=
  formalSpectrumMap_comp hR hprod (continuousHomPi B S hS E ψ)
    (continuousHomPiProjection B S hS E i) (ψ i) (RingHom.ext fun _ ↦ rfl)

omit [∀ (i : ι), IsLinearTopology (A i) (A i)] in
/-- **Joint surjectivity of finitely many formal spectra over a base, read on the product.**
Let `D` present a chart and let `E i` present finitely many charts receiving continuous
homomorphisms `ψ i` from it. If a family of sheaves identified with the `Spf (E i)` is jointly
surjective over `Spf D` — the morphism out of its coproduct being a surjection of fppf
sheaves — then the single morphism `Spf (∀ i, A i) ⟶ Spf D` induced by the product of the
`ψ i` is surjective.

This is the input that condition (1) of **Stacks 0AN9** takes: the surjectivity of one formal
spectrum map. Each member of the jointly surjective family factors through
`Spf (∀ i, A i)` along the formal spectrum of the `i`-th projection, and a morphism through
which a jointly surjective family factors is surjective on points. -/
theorem isSurjective_formalSpectrumMap_continuousHomPi
    (hprod : TopologicalRing.IsWeaklyAdmissible (∀ i, A i))
    (hR : TopologicalRing.IsWeaklyAdmissible R) {D : QuotientSystem B S hS R}
    (E : ∀ i, QuotientSystem B S hS (A i)) (ψ : ∀ i, ContinuousHom D (E i))
    {I : Type (u + 1)} {Y : I → FppfSheaf B S hS} (κ : I → ι)
    (e : ∀ j, Y j ≅ formalSpectrum (E (κ j))) (y : ∀ j, Y j ⟶ formalSpectrum D)
    (hy : ∀ j, y j = (e j).hom ≫ formalSpectrumMap hR (ψ (κ j)))
    (hcover : Sheaf.IsLocallySurjective (Sigma.desc y)) :
    IsSurjective B S hS (formalSpectrumMap hR (continuousHomPi B S hS E ψ)) := by
  refine isSurjective_of_isLocallySurjective_sigmaDesc_of_factors B S hS y hcover
    (fun j ↦ (e j).hom ≫ formalSpectrumMap hprod
      (continuousHomPiProjection B S hS E (κ j))) fun j ↦ ?_
  rw [Category.assoc, formalSpectrumMap_continuousHomPiProjection_comp, hy]

end Surjectivity

end FiniteProduct

end AlgebraicGeometry.FormalSpace

end
