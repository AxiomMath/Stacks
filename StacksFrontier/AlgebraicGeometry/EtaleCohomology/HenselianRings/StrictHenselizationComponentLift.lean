module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.FiniteBaseChangeStrictHenselization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StrictlyHenselianVanishing
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.StrictlyHenselianVanishing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Lifting a geometric point from a strictly henselian local scheme into its étale neighborhoods

Let `x` be a geometric point of a scheme `X` which factors through a strictly henselian local
scheme, say `x = p ≫ c` with `c : Spec R ⟶ X` and `p` hitting the closed point of `R`. Then every
étale neighborhood of `x` receives a morphism from `Spec R` over `X` carrying `p` to the chosen
lift: an étale scheme over `Spec R` with a point over the closed point has a section, because `R`
is henselian with separably closed residue field.

Applied to the components of the decomposition of `X ×_Y Spec(𝒪^{sh}_{Y,y})` for a finite morphism
`f : X ⟶ Y` — the decomposition of
`AlgebraicGeometry.finite_baseChange_strictHenselization_decomposition` — this says that the
component at a lift `x` of `y` maps into *every* étale neighborhood of `x`.

## Main results

* `AlgebraicGeometry.exists_hom_of_strictlyHenselian` — the lifting property above, for an
  arbitrary étale morphism and compatible point.
* `AlgebraicGeometry.base_eq_closedPoint_of_isIntegralHom` — a point of a local scheme whose
  image under an integral morphism of local schemes is the closed point is itself the closed
  point.
* `AlgebraicGeometry.isClosedImmersion_sigmaι_spec` — the inclusion of a component of a finite
  coproduct of affine schemes is a closed immersion, with
  `AlgebraicGeometry.isIntegralHom_sigmaι_spec` its integrality.
* `AlgebraicGeometry.strictHenselizationComponentHom` and
  `AlgebraicGeometry.finite_strictHenselizationComponentHom` — the structure homomorphism of a
  component of the decomposition over the étale local ring, and its finiteness.
* `AlgebraicGeometry.exists_hom_etaleNeighborhood_of_strictlyHenselian` and
  `AlgebraicGeometry.exists_hom_etaleNeighborhood_of_isIntegralHom` — the same statements for an
  étale neighborhood of the small étale site, i.e. for an object of the category of elements of
  `AlgebraicGeometry.geometricPointFiber`, which is the index category of the étale stalk.
* `AlgebraicGeometry.geometricPointToStrictHenselization_base_default` — the canonical point of
  the strict henselization lies over the closed point.
* `AlgebraicGeometry.exists_hom_strictHenselizationComponent_etaleNeighborhood` — the component
  of the decomposition at a lift maps over `X` into every étale neighborhood of that lift,
  compatibly with the chosen points.
* `AlgebraicGeometry.not_exists_hom_pullback_of_disjoint_section` and
  `AlgebraicGeometry.not_cofinal_pullback_of_two_lifts` — the corresponding statement for the
  whole base change `U ×_Y X`, rather than for its component at the lift, is false, already for
  a finite morphism: a second lift of the geometric point obstructs it.

## References

* [Stacks Project, Tag 03QP](https://stacks.math.columbia.edu/tag/03QP)
* [Stacks Project, Tag 03QO](https://stacks.math.columbia.edu/tag/03QO)
* [Stacks Project, Tag 04GG](https://stacks.math.columbia.edu/tag/04GG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry

/-! ### Lifting a geometric point into an étale neighborhood -/

/-- **A strictly henselian local scheme through which a geometric point factors maps into every
étale neighborhood of that point.** Here `c : Spec R ⟶ X` and `p` exhibit the geometric point `x`
as factoring through the strictly henselian local scheme `Spec R`, with `p` hitting the closed
point, and `w : W ⟶ X` is étale with a lift `v` of `x`. -/
@[sga "4 VIII 4.2" "(i)"]
public theorem exists_hom_of_strictlyHenselian {X : Scheme.{u}} (x : GeometricPoint X)
    {R : Type u} [CommRing R] [StrictlyHenselianLocalRing R]
    (c : Spec (.of R) ⟶ X) (p : x.source ⟶ Spec (.of R)) (hp : p ≫ c = x.hom)
    (hcl : p (default : x.source) = IsLocalRing.closedPoint R)
    {W : Scheme.{u}} (w : W ⟶ X) [Etale w] (v : x.source ⟶ W) (hv : v ≫ w = x.hom) :
    ∃ t : Spec (.of R) ⟶ W, t ≫ w = c ∧ p ≫ t = v := by
  let s : GeometricPoint (Spec (.of R)) := { residueField := x.residueField, hom := p }
  have hs : s.LiesOver (IsLocalRing.closedPoint R) := hcl
  let z : x.source ⟶ pullback w c := pullback.lift v p (hv.trans hp.symm)
  have hz : z ≫ pullback.snd w c = s.hom := pullback.lift_snd _ _ _
  obtain ⟨t, ht, htp⟩ := Stacks.StrictlyHenselian.exists_etale_section s hs
    (pullback w c) (pullback.snd w c) z hz
  refine ⟨t ≫ pullback.fst w c, ?_, ?_⟩
  · calc t ≫ pullback.fst w c ≫ w = t ≫ pullback.snd w c ≫ c := by rw [pullback.condition]
      _ = c := by rw [← Category.assoc, ht, Category.id_comp]
  · calc p ≫ t ≫ pullback.fst w c = z ≫ pullback.fst w c := by rw [← Category.assoc, htp]
      _ = v := pullback.lift_fst _ _ _

/-- **A point of a local scheme lying over the closed point of a local scheme it is integral over
is the closed point.** -/
public theorem base_eq_closedPoint_of_isIntegralHom {A R : Type u} [CommRing A] [CommRing R]
    [IsLocalRing A] [IsLocalRing R] (h : Spec (.of A) ⟶ Spec (.of R)) [IsIntegralHom h]
    {Z : Scheme.{u}} (p : Z ⟶ Spec (.of A)) (z : Z)
    (hz : (p ≫ h) z = IsLocalRing.closedPoint R) :
    p z = IsLocalRing.closedPoint A := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective h
  have hiφ : IsIntegralHom (Spec.map φ) := hφ ▸ ‹IsIntegralHom h›
  let : Algebra R A := φ.hom.toAlgebra
  have halg : (algebraMap R A) = φ.hom := RingHom.algebraMap_toAlgebra _
  have hint : Algebra.IsIntegral R A := Algebra.isIntegral_def.mpr fun a => by
    change (algebraMap R A).IsIntegralElem a
    rw [halg]
    exact (IsIntegralHom.SpecMap_iff (φ := φ)).mp hiφ a
  have hprime : ((p z).asIdeal).IsPrime := (p z).isPrime
  have hcomap : Ideal.comap (algebraMap R A) (p z).asIdeal = IsLocalRing.maximalIdeal R := by
    have h1 : ((p ≫ h) z).asIdeal = Ideal.comap (algebraMap R A) (p z).asIdeal := by
      rw [Scheme.Hom.comp_apply, ← hφ, Spec.map_apply, halg]
      rfl
    rw [← h1, hz]
    rfl
  have hcm : (Ideal.comap (algebraMap R A) (p z).asIdeal).IsMaximal :=
    hcomap ▸ IsLocalRing.maximalIdeal.isMaximal R
  have hmax : ((p z).asIdeal).IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := R) (S := A) (p z).asIdeal hcm
  exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hmax)

/-- **The lifting property, with the hypothesis on the point supplied by integrality.** The
geometric point `x` factors through the strictly henselian local scheme `Spec A`, which is
integral over a local scheme `Spec R`, and the image of the chosen point in `Spec R` is the closed
point; then every étale neighborhood of `x` receives `Spec A` over `X`. -/
@[sga "4 VIII 4.2" "(i)"]
public theorem exists_hom_of_strictlyHenselian_of_isIntegralHom {X : Scheme.{u}}
    (x : GeometricPoint X) {A R : Type u} [CommRing A] [CommRing R]
    [StrictlyHenselianLocalRing A] [IsLocalRing R]
    (c : Spec (.of A) ⟶ X) (h : Spec (.of A) ⟶ Spec (.of R)) [IsIntegralHom h]
    (p : x.source ⟶ Spec (.of A)) (hp : p ≫ c = x.hom)
    (hq : (p ≫ h) (default : x.source) = IsLocalRing.closedPoint R)
    {W : Scheme.{u}} (w : W ⟶ X) [Etale w] (v : x.source ⟶ W) (hv : v ≫ w = x.hom) :
    ∃ t : Spec (.of A) ⟶ W, t ≫ w = c ∧ p ≫ t = v :=
  exists_hom_of_strictlyHenselian x c p hp
    (base_eq_closedPoint_of_isIntegralHom h p default hq) w v hv

/-! ### Étale neighborhoods in the small étale site -/

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) (x : GeometricPoint X)

/-- **Every étale neighborhood of a geometric point in the small étale site receives a strictly
henselian local scheme through which the point factors.** Here an étale neighborhood of `x` is an
object of the category of elements of `AlgebraicGeometry.geometricPointFiber`. -/
@[sga "4 VIII 4.2" "(i)"]
public theorem exists_hom_etaleNeighborhood_of_strictlyHenselian
    {R : Type u} [CommRing R] [StrictlyHenselianLocalRing R]
    (c : Spec (.of R) ⟶ X) (p : x.source ⟶ Spec (.of R)) (hp : p ≫ c = x.hom)
    (hcl : p (default : x.source) = IsLocalRing.closedPoint R)
    (W : (geometricPointFiber B X hX x).Elements) :
    ∃ t : Spec (.of R) ⟶ (SmallEtale.toScheme B X hX).obj W.1,
      t ≫ B.inclusion.map W.1.obj.hom = c ∧ p ≫ t = W.2.1 :=
  exists_hom_of_strictlyHenselian x c p hp hcl (B.inclusion.map W.1.obj.hom) W.2.1 W.2.2

/-- **The same, with the hypothesis on the point supplied by integrality.** -/
public theorem exists_hom_etaleNeighborhood_of_isIntegralHom
    {A R : Type u} [CommRing A] [CommRing R] [StrictlyHenselianLocalRing A] [IsLocalRing R]
    (c : Spec (.of A) ⟶ X) (h : Spec (.of A) ⟶ Spec (.of R)) [IsIntegralHom h]
    (p : x.source ⟶ Spec (.of A)) (hp : p ≫ c = x.hom)
    (hq : (p ≫ h) (default : x.source) = IsLocalRing.closedPoint R)
    (W : (geometricPointFiber B X hX x).Elements) :
    ∃ t : Spec (.of A) ⟶ (SmallEtale.toScheme B X hX).obj W.1,
      t ≫ B.inclusion.map W.1.obj.hom = c ∧ p ≫ t = W.2.1 :=
  exists_hom_etaleNeighborhood_of_strictlyHenselian B X hX x c p hp
    (base_eq_closedPoint_of_isIntegralHom h p default hq) W

/-! ### The components of the decomposition over the strict henselization -/

/-- The inclusion of a component of a finite coproduct of affine schemes is a closed
immersion. -/
public instance isClosedImmersion_sigmaι_spec {ι : Type u} [Finite ι] (A : ι → CommRingCat.{u})
    (i : ι) : IsClosedImmersion (Sigma.ι (fun j => Spec (A j)) i) := by
  have hcl : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun j => (A j : Type u)) i))) :=
    IsClosedImmersion.spec_of_surjective _ (Function.surjective_eval i)
  have hι : Sigma.ι (fun j => Spec (A j)) i =
      Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun j => (A j : Type u)) i)) ≫
        inv (sigmaSpec A) := by
    rw [← ι_sigmaSpec A i, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [hι]
  infer_instance

/-- The inclusion of a component of a finite coproduct of affine schemes is integral. -/
public instance isIntegralHom_sigmaι_spec {ι : Type u} [Finite ι] (A : ι → CommRingCat.{u})
    (i : ι) : IsIntegralHom (Sigma.ι (fun j => Spec (A j)) i) :=
  inferInstance

/-- The ring homomorphism from the étale local ring of `Y` at `y` to `A i` whose spectrum is the
structure morphism of the component `Spec (A i)` of the decomposition `e` over the strict
henselization. -/
public def strictHenselizationComponentHom {Y : Scheme.{u}} (f : X ⟶ Y)
    (hY : B.Contains Y) (y : GeometricPoint Y) {ι : Type u} (A : ι → CommRingCat.{u})
    (e : (∐ fun i => Spec (A i)) ≅ pullback f (strictHenselizationToBase B Y hY y)) (i : ι) :
    CommRingCat.of ↥(etaleLocalRing B Y hY y) ⟶ A i :=
  Spec.preimage (Sigma.ι (fun j => Spec (A j)) i ≫ e.hom ≫
    pullback.snd f (strictHenselizationToBase B Y hY y))

/-- The structure homomorphism of a component is the one whose spectrum is the component's
structure morphism. -/
public theorem specMap_strictHenselizationComponentHom {Y : Scheme.{u}} (f : X ⟶ Y)
    (hY : B.Contains Y) (y : GeometricPoint Y) {ι : Type u} (A : ι → CommRingCat.{u})
    (e : (∐ fun i => Spec (A i)) ≅ pullback f (strictHenselizationToBase B Y hY y)) (i : ι) :
    Spec.map (strictHenselizationComponentHom B X f hY y A e i) =
      Sigma.ι (fun j => Spec (A j)) i ≫ e.hom ≫
        pullback.snd f (strictHenselizationToBase B Y hY y) :=
  Spec.map_preimage _

/-- Each component of the decomposition is finite over the étale local ring. -/
public theorem finite_strictHenselizationComponentHom {Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] (hY : B.Contains Y) (y : GeometricPoint Y) {ι : Type u} [Finite ι]
    (A : ι → CommRingCat.{u})
    (e : (∐ fun i => Spec (A i)) ≅ pullback f (strictHenselizationToBase B Y hY y)) (i : ι) :
    (strictHenselizationComponentHom B X f hY y A e i).hom.Finite := by
  rw [← IsFinite.SpecMap_iff, specMap_strictHenselizationComponentHom]
  infer_instance

/-- The étale local ring at a geometric point is a strictly henselian local ring. -/
public instance strictlyHenselianLocalRing_etaleLocalRing (s : GeometricPoint X) :
    StrictlyHenselianLocalRing ↥(etaleLocalRing B X hX s) :=
  etaleLocalRing_strictHenselian B X hX s

/-- The canonical point of the strict henselization at a geometric point lies over the closed
point of the étale local ring. -/
public theorem geometricPointToStrictHenselization_base_default (s : GeometricPoint X) :
    (geometricPointToStrictHenselization B X hX s) (default : s.source) =
      IsLocalRing.closedPoint ↥(etaleLocalRing B X hX s) := by
  have hloc : IsLocalHom (structureSheafStalkToGeometricField B X hX s) :=
    structureSheafStalkToGeometricField_isLocalHom B X hX s
  have hker : RingHom.ker (structureSheafStalkToGeometricField B X hX s) =
      IsLocalRing.maximalIdeal ↥(etaleLocalRing B X hX s) := by
    refine le_antisymm (IsLocalRing.le_maximalIdeal fun htop => ?_) fun a ha => ?_
    · have h1 : (1 : ↥(etaleLocalRing B X hX s)) ∈
          RingHom.ker (structureSheafStalkToGeometricField B X hX s) := htop ▸ Submodule.mem_top
      exact one_ne_zero ((map_one _).symm.trans (RingHom.mem_ker.mp h1))
    · refine RingHom.mem_ker.mpr ?_
      by_contra hzero
      exact (IsLocalRing.notMem_maximalIdeal.mpr
        (hloc.map_nonunit a (isUnit_iff_ne_zero.mpr hzero))) ha
  refine PrimeSpectrum.ext ?_
  change Ideal.comap (structureSheafStalkToGeometricField B X hX s)
      (default : s.source).asIdeal = IsLocalRing.maximalIdeal ↥(etaleLocalRing B X hX s)
  rw [show (default : s.source).asIdeal = ⊥ from rfl, ← RingHom.ker_eq_comap_bot, hker]

/-- **The component of the decomposition at a lift maps over `X` into every étale neighborhood of
that lift.** Here `e` decomposes `X ×_Y Spec(𝒪^{sh}_{Y,y})` into the components `Spec (A i)`,
and `i` runs over the lifts of the geometric point `y`. -/
public theorem exists_hom_strictHenselizationComponent_etaleNeighborhood
    {Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] (hY : B.Contains Y) (y : GeometricPoint Y)
    [Finite {g : y.source ⟶ X // g ≫ f = y.hom}]
    (A : {g : y.source ⟶ X // g ≫ f = y.hom} → CommRingCat.{u})
    [∀ i, StrictlyHenselianLocalRing (A i)]
    (e : (∐ fun i => Spec (A i)) ≅ pullback f (strictHenselizationToBase B Y hY y))
    (p : ∀ i, y.source ⟶ Spec (A i))
    (hfst : ∀ i, p i ≫ Sigma.ι (fun j => Spec (A j)) i ≫ e.hom ≫
      pullback.fst f (strictHenselizationToBase B Y hY y) = i.val)
    (hsnd : ∀ i, p i ≫ Sigma.ι (fun j => Spec (A j)) i ≫ e.hom ≫
      pullback.snd f (strictHenselizationToBase B Y hY y) =
        geometricPointToStrictHenselization B Y hY y)
    (i : {g : y.source ⟶ X // g ≫ f = y.hom})
    (W : (geometricPointFiber B X hX
      ({ residueField := y.residueField, hom := i.val } : GeometricPoint X)).Elements) :
    ∃ t : Spec (A i) ⟶ (SmallEtale.toScheme B X hX).obj W.1,
      t ≫ B.inclusion.map W.1.obj.hom =
        Sigma.ι (fun j => Spec (A j)) i ≫ e.hom ≫
          pullback.fst f (strictHenselizationToBase B Y hY y) ∧
      p i ≫ t = W.2.1 := by
  have hq : (p i ≫ Sigma.ι (fun j => Spec (A j)) i ≫ e.hom ≫
        pullback.snd f (strictHenselizationToBase B Y hY y))
      (default : ({ residueField := y.residueField, hom := i.val } :
        GeometricPoint X).source) =
      IsLocalRing.closedPoint ↥(etaleLocalRing B Y hY y) := by
    rw [hsnd i]
    exact geometricPointToStrictHenselization_base_default B Y hY y
  exact exists_hom_etaleNeighborhood_of_isIntegralHom B X hX
    ({ residueField := y.residueField, hom := i.val } : GeometricPoint X)
    (Sigma.ι (fun j => Spec (A j)) i ≫ e.hom ≫
      pullback.fst f (strictHenselizationToBase B Y hY y))
    (Sigma.ι (fun j => Spec (A j)) i ≫ e.hom ≫
      pullback.snd f (strictHenselizationToBase B Y hY y))
    (p i) (hfst i) hq W

/-! ### The whole base change is not cofinal -/

/-- If `σ : Y ⟶ X` is a section of `f : X ⟶ Y` whose image misses the image of `w : W ⟶ X`, then
for no `U` over `Y` with a point does the base change `U ×_Y X` receive a morphism to `W` over
`X`. -/
public theorem not_exists_hom_pullback_of_disjoint_section {X Y W U : Scheme.{u}}
    (f : X ⟶ Y) (σ : Y ⟶ X) (hσ : σ ≫ f = 𝟙 Y) (w : W ⟶ X)
    (hdisj : ∀ (a : W) (b : Y), w a ≠ σ b)
    (g : U ⟶ Y) (u : U) (h : pullback g f ⟶ W) :
    h ≫ w ≠ pullback.snd g f := by
  intro he
  let ζ : U ⟶ pullback g f := pullback.lift (𝟙 U) (g ≫ σ) (by
    rw [Category.id_comp, Category.assoc, hσ, Category.comp_id])
  have h1 : ζ ≫ (h ≫ w) = g ≫ σ := by rw [he, pullback.lift_snd]
  refine hdisj (h (ζ u)) (g u) ?_
  simpa only [Scheme.Hom.comp_apply] using congrArg (fun k : U ⟶ X => k u) h1

/-- For the split double cover `f : Y ⨿ Y ⟶ Y`, which is finite, the first summand is an étale
neighborhood of the lift `y ≫ coprod.inl` of a geometric point `y` of `Y`, the composite
`y ≫ coprod.inr` is a second lift of `y`, and no base change of a scheme over `Y` carrying a point
receives a morphism to the first summand over `Y ⨿ Y`. -/
public theorem not_cofinal_pullback_of_two_lifts {Y : Scheme.{u}} (y : GeometricPoint Y) :
    IsFinite (coprod.desc (𝟙 Y) (𝟙 Y)) ∧ Etale (coprod.inl : Y ⟶ Y ⨿ Y) ∧
      (y.hom ≫ (coprod.inl : Y ⟶ Y ⨿ Y)) ≫ coprod.desc (𝟙 Y) (𝟙 Y) = y.hom ∧
      (y.hom ≫ (coprod.inr : Y ⟶ Y ⨿ Y)) ≫ coprod.desc (𝟙 Y) (𝟙 Y) = y.hom ∧
      ∀ (U : Scheme.{u}) (g : U ⟶ Y) (_ : U)
        (h : pullback g (coprod.desc (𝟙 Y) (𝟙 Y)) ⟶ Y),
        h ≫ (coprod.inl : Y ⟶ Y ⨿ Y) ≠ pullback.snd g (coprod.desc (𝟙 Y) (𝟙 Y)) := by
  refine ⟨inferInstance, inferInstance, ?_, ?_, fun U g u h => ?_⟩
  · rw [Category.assoc, coprod.inl_desc, Category.comp_id]
  · rw [Category.assoc, coprod.inr_desc, Category.comp_id]
  · exact not_exists_hom_pullback_of_disjoint_section _ coprod.inr (coprod.inr_desc _ _) _
      (fun a b => inl_ne_inr Y Y a b) g u h

end AlgebraicGeometry

end
