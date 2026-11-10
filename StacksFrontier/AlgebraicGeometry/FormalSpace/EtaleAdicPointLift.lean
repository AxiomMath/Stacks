module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableEtaleFormallyEtale
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SquareZeroAdicTower
public import StacksFrontier.AlgebraicGeometry.FormalSpace.MapsToAffine
public import StacksFrontier.AlgebraicGeometry.FormalSpace.WeakIdealPresentation
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveEtaleSurjective
public import StacksCore.Tactic.StacksAttribute
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.FieldTheory.PrimitiveElement
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.OverField
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedEtaleSiteMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedPoints
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdmissibleAdic

/-!
# Lifting an adic point along a representable étale morphism (Stacks 0AQU)

Let `S` be a scheme contained in a big fppf site `B`. **Stacks 0AQU** says that a morphism
`f : X ⟶ Y` of formal algebraic spaces over `S` which is representable by algebraic spaces,
étale and surjective is rig-surjective: every adic point `Spf R ⟶ Y` out of the formal spectrum
of a complete discrete valuation ring lifts to `X` after an extension `R ⊂ R'` of complete
discrete valuation rings.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_lift_formalSpectrum_of_formallyEtale`: a morphism out of
  the formal spectrum of an adic ring lifts along a formally étale morphism as soon as its
  restriction to the closed stage does.
* `AlgebraicGeometry.FormalSpace.exists_finite_separable_section_of_pointsULift_pullback`: a
  point of `Spf R ×_Y X` gives a section of `X` over a finite separable extension of the residue
  field of `R`, over `p`.
* `AlgebraicGeometry.FormalSpace.exists_etale_root_of_finite_separable`: a finite separable
  extension of a residue field is cut out by a standard étale algebra.
* `AlgebraicGeometry.FormalSpace.exists_lift_of_pointsULift_pullback_of_isRepresentableEtale`:
  the lifting step of Stacks 0AQU from a point of the fibre product.
* `AlgebraicGeometry.FormalSpace.isRigSurjective_of_isSurjective_of_isRepresentableEtale`:
  **Stacks 0AQU**.

## Implementation notes

The source picks an affine étale chart `V` of `Z = Spf R ×_Y X`, which needs `Z` to be a formal
algebraic space (Stacks 0AJ3, which rests on Stacks 0AIU), and reads `V ⟶ Spf R` as `Spf` of an
étale algebra by Stacks 0AN8. Here the chart is never formed. The base change of `f` to the
residue field `κ` of `R` is an algebraic space étale over `Spec κ`, so a point of `Z` gives a
point over a finite separable `L / κ` (Stacks 02GL). A standard étale `R`-algebra lifting `L`
maps to a complete discrete valuation ring `R'` (Stacks 00PH, 0AP1), which receives `L` in its
residue field. The closed stage of `Spf R'` therefore maps to `X` over `p`, and that map extends
to `Spf R'` because `f` is formally étale
(`AlgebraicGeometry.FormalSpace.formallyEtale_hom_of_isRepresentableEtale`, Stacks 0616) and the
stages of `Spf R'` form a tower of square-zero thickenings.

## References

* [Stacks Project, Tag 0AQU](https://stacks.math.columbia.edu/tag/0AQU)
* [Stacks Project, Tag 0AIF](https://stacks.math.columbia.edu/tag/0AIF)
* [Stacks Project, Tag 02GL](https://stacks.math.columbia.edu/tag/02GL)
* [Stacks Project, Tag 0616](https://stacks.math.columbia.edu/tag/0616)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.FormalSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section CofinalStages

variable {R : Type u} [CommRing R] [TopologicalSpace R] (D : QuotientSystem B S hS R)
  (J : ℕ → { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I })
  (hmono : ∀ n, (J (n + 1)).1 ≤ (J n).1)

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- Two morphisms out of a formal spectrum agree as soon as they agree on a sequence of quotient
stages cofinal among all of them. -/
theorem formalSpectrum_hom_ext_of_cofinal
    (hcofinal : ∀ I : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      ∃ n, (J n).1 ≤ I.1)
    {Y : FppfSheaf B S hS} {a b : formalSpectrum D ⟶ Y}
    (h : ∀ n, formalSpectrumInclusion D (OrderDual.toDual (J n)) ≫ a =
      formalSpectrumInclusion D (OrderDual.toDual (J n)) ≫ b) :
    a = b := by
  refine colimit.hom_ext fun K => ?_
  obtain ⟨n, hn⟩ := hcofinal (OrderDual.ofDual K)
  let g : K ⟶ OrderDual.toDual (J n) :=
    homOfLE (OrderDual.le_toDual.mpr (Subtype.coe_le_coe.mp hn))
  exact (colimit.w_assoc (formalSpectrumDiagram D) g a).symm.trans
    ((congrArg (fun c => (formalSpectrumDiagram D).map g ≫ c) (h n)).trans
      (colimit.w_assoc (formalSpectrumDiagram D) g b))

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- A compatible family of morphisms out of a sequence of quotient stages cofinal among all of
them determines a morphism out of the formal spectrum. -/
theorem exists_formalSpectrum_hom_of_cofinal
    (hcofinal : ∀ I : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      ∃ n, (J n).1 ≤ I.1)
    {Y : FppfSheaf B S hS}
    (x : ∀ n, (formalSpectrumDiagram D).obj (OrderDual.toDual (J n)) ⟶ Y)
    (hx : ∀ n, (formalSpectrumDiagram D).map
      (homOfLE (show OrderDual.toDual (J n) ≤ OrderDual.toDual (J (n + 1)) from hmono n)) ≫
        x (n + 1) = x n) :
    ∃ q : formalSpectrum D ⟶ Y,
      ∀ n, formalSpectrumInclusion D (OrderDual.toDual (J n)) ≫ q = x n := by
  have hJ : Antitone fun n => (J n).1 := antitone_nat_of_succ_le hmono
  have hPmono : Monotone (fun n => OrderDual.toDual (J n)) := fun _ _ h => hJ h
  let P := hPmono.functor
  have hfinal : P.Final :=
    (Monotone.final_functor_iff hPmono).2 fun I => hcofinal (OrderDual.ofDual I)
  let G := formalSpectrumDiagram D
  let H := P ⋙ G
  have hnat (n k : ℕ) (h : n ≤ k) : H.map (homOfLE h) ≫ x k = x n := by
    induction k, h using Nat.le_induction with
    | base => simp [H]
    | succ k hk ih =>
      have hcat : homOfLE hk ≫ homOfLE (Nat.le_succ k) =
          homOfLE (hk.trans (Nat.le_succ k)) := Subsingleton.elim _ _
      rw [← hcat, Functor.map_comp, Category.assoc]
      have hstep : H.map (homOfLE (Nat.le_succ k)) ≫ x (k + 1) = x k := hx k
      rw [hstep, ih]
  let c : Cocone H :=
    { pt := Y
      ι := { app := x
             naturality := fun n k f => by
               rw [Subsingleton.elim f (homOfLE (leOfHom f))]
               simpa using hnat n k (leOfHom f) } }
  refine ⟨(Functor.Final.colimitIso P G).inv ≫ colimit.desc H c, fun n => ?_⟩
  change colimit.ι G (P.obj n) ≫ (Functor.Final.colimitIso P G).inv ≫ colimit.desc H c = x n
  rw [← Category.assoc, Functor.Final.ι_colimitIso_inv P G n]
  exact colimit.ι_desc c n

end CofinalStages

section AdicLift

variable {W : Type u} [CommRing W] [TopologicalSpace W] [IsTopologicalRing W] {I : Ideal W}

/-- The positive powers of an ideal defining the topology are cofinal among the weak ideals of
definition: a weak ideal of definition is open, so it contains a power of the ideal. -/
theorem exists_adicStage_le (hadic : _root_.IsAdic I)
    (K : { K : Ideal W // TopologicalRing.IsWeakIdealOfDefinition K }) :
    ∃ n, (adicStage hadic n).1 ≤ K.1 := by
  obtain ⟨n, hn⟩ := (isAdic_iff.mp hadic).2 _ (K.2.1.mem_nhds K.1.zero_mem)
  exact ⟨n, (Ideal.pow_le_pow_right (Nat.le_succ n)).trans hn⟩

/-- If `a'` restricts to `a` along `t`, then the section of `Y` attached to `a ≫ q` is the
restriction along `t` of the section attached to `a' ≫ q`. -/
private theorem sectionEquiv_comp_eq_map {T T' : BigFppfOver B S hS} (t : T ⟶ T')
    {A Y : FppfSheaf B S hS} {a : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T ⟶ A}
    {a' : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T' ⟶ A}
    (h : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map t ≫ a' = a) (q : A ⟶ Y) :
    Sheaf.sectionEquiv (BigFppfOver.topology B S hS) (a ≫ q) =
      Y.obj.map t.op (Sheaf.sectionEquiv (BigFppfOver.topology B S hS) (a' ≫ q)) := by
  rw [← h, Category.assoc, Sheaf.sectionEquiv_map_comp]

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- **An adic point lifts along a formally étale morphism once its closed stage does.** Let
`f : X ⟶ Y` be a morphism of fppf sheaves over `S` which is formally étale, let `W` be a
topological ring carrying the `I`-adic topology with a quotient system `D`, and let
`q : Spf W ⟶ Y`. A lift of the restriction of `q` to the stage `Spec (W ⧸ I)` extends to a lift
`Spf W ⟶ X` of `q`.

The lift is built stage by stage along the tower `Spec (W ⧸ Iⁿ⁺¹) ⊂ Spec (W ⧸ Iⁿ⁺²)` of
square-zero thickenings, and the powers of `I` are cofinal among the weak ideals of
definition. -/
theorem exists_lift_formalSpectrum_of_formallyEtale {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hf : Space.FormallyEtale f.hom) (hadic : _root_.IsAdic I) (D : QuotientSystem B S hS W)
    (q : formalSpectrum D ⟶ Y)
    (z₀ : (formalSpectrumDiagram D).obj (OrderDual.toDual (adicStage hadic 0)) ⟶ X)
    (hz₀ : z₀ ≫ f = formalSpectrumInclusion D (OrderDual.toDual (adicStage hadic 0)) ≫ q) :
    ∃ x : formalSpectrum D ⟶ X, x ≫ f = q := by
  classical
  let Jt := BigFppfOver.topology B S hS
  let T : ℕ → BigFppfOver B S hS := fun n =>
    (BigAffineFppf.inclusion B S hS).obj (D.stage (adicStage hadic n))
  let ι : ∀ n, (formalSpectrumDiagram D).obj (OrderDual.toDual (adicStage hadic n)) ⟶
      formalSpectrum D := fun n => formalSpectrumInclusion D (OrderDual.toDual (adicStage hadic n))
  let g : ∀ n, OrderDual.toDual (adicStage hadic n) ⟶ OrderDual.toDual (adicStage hadic (n + 1)) :=
    fun n => homOfLE (adicStage_le_succ hadic n)
  let y : ∀ n, Y.obj.obj (op (T n)) := fun n => Sheaf.sectionEquiv Jt (ι n ≫ q)
  have hy : ∀ n, Y.obj.map (adicTowerMap D hadic n).op (y (n + 1)) = y n := fun n =>
    (sectionEquiv_comp_eq_map _ (colimit.w (formalSpectrumDiagram D) (g n)) q).symm
  obtain ⟨z, -, hz, hzy⟩ := exists_compatible_lifts_adicTower_of_formallyEtale f.hom hf D hadic
    y hy (Sheaf.sectionEquiv Jt z₀)
    ((Sheaf.sectionEquiv_comp Jt z₀ f).symm.trans (congrArg (Sheaf.sectionEquiv Jt) hz₀))
  let zm : ∀ n, (formalSpectrumDiagram D).obj (OrderDual.toDual (adicStage hadic n)) ⟶ X :=
    fun n => (Sheaf.sectionEquiv Jt).symm (z n)
  have hzms : ∀ n, Sheaf.sectionEquiv Jt (zm n) = z n := fun n => Equiv.apply_symm_apply _ _
  have hzm : ∀ n, (formalSpectrumDiagram D).map (g n) ≫ zm (n + 1) = zm n := fun n =>
    (Sheaf.sectionEquiv Jt).injective <|
      (Sheaf.sectionEquiv_map_comp Jt (adicTowerMap D hadic n) (zm (n + 1))).trans
        ((congrArg _ (hzms (n + 1))).trans ((hz n).trans (hzms n).symm))
  have hzmf : ∀ n, zm n ≫ f = ι n ≫ q := fun n =>
    (Sheaf.sectionEquiv Jt).injective <|
      (Sheaf.sectionEquiv_comp Jt (zm n) f).trans ((congrArg _ (hzms n)).trans (hzy n))
  obtain ⟨x, hx⟩ := exists_formalSpectrum_hom_of_cofinal D (adicStage hadic)
    (adicStage_le_succ hadic) (exists_adicStage_le hadic) zm hzm
  exact ⟨x, formalSpectrum_hom_ext_of_cofinal D (adicStage hadic) (exists_adicStage_le hadic)
    fun n => (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ f) (hx n)).trans (hzmf n))⟩

end AdicLift

section ResiduePoint

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- **A representable étale morphism over a field point has a finite separable point.** Let
`f : X ⟶ Y` be representable by algebraic spaces and étale, let `y` be a section of `Y` over
the spectrum of a field `k` of the site, and suppose a section of `X` over a nonempty object
`V` of the site lies over the restriction of `y` along some `V ⟶ Spec k`. Then there is a
finite separable extension `L / k` and a section of `X` over `Spec L` lying over the
restriction of `y` to `Spec L`.

The base change of `f` along `y` is an algebraic space étale over `Spec k`; the given section
over `V` makes it nonempty, hence so is any atlas `U` of it, and `U` is étale over `Spec k`, so
a disjoint union of spectra of finite separable extensions of `k` (Stacks 02GL). -/
theorem exists_finite_separable_section_of_isRepresentableEtale {X Y : FppfSheaf B S hS}
    (f : X ⟶ Y) (hf : IsRepresentableEtale B S hS f) (k : Type u) [Field k]
    (hk : B.Contains (Spec (.of k))) (pk : Spec (.of k) ⟶ S)
    (y : Y.obj.obj (op (specOver (hS := hS) hk pk).1))
    (V : BigFppfOver B S hS) (hV : Nonempty ((BigFppfOver.toScheme B S hS).obj V))
    (t : V ⟶ (specOver (hS := hS) hk pk).1) (x : X.obj.obj (op V))
    (hx : f.hom.app (op V) x = Y.obj.map t.op y) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L) (_ : Module.Finite k L)
      (_ : Algebra.IsSeparable k L) (hL : B.Contains (Spec (.of L)))
      (b : X.obj.obj (op (specOver (hS := hS) hL
        (Spec.map (CommRingCat.ofHom (algebraMap k L)) ≫ pk)).1)),
      f.hom.app _ b = Y.obj.map (Over.homMk (ObjectProperty.homMk
        (Spec.map (CommRingCat.ofHom (algebraMap k L)))) (by rfl) :
          (specOver (hS := hS) hL (Spec.map (CommRingCat.ofHom (algebraMap k L)) ≫ pk)).1 ⟶
            (specOver (hS := hS) hk pk).1).op y := by
  classical
  let C := BigFppfOver.toScheme B S hS
  let T₀ := (specOver (hS := hS) hk pk).1
  let ξ : (uliftYoneda.{u + 1}).obj T₀ ⟶ Y.obj := uliftYonedaEquiv.symm y
  obtain ⟨U, φ, hφs, hφe⟩ := (hf.1 T₀ ξ).exists_atlas
  obtain ⟨u, hu⟩ := (ULiftYoneda.fullyFaithful.{u + 1} (C := BigFppfOver B S hS)).map_surjective
    (φ ≫ pullback.fst ξ f.hom)
  have huet : Etale (C.map u) := by
    have h := hf.2 T₀ ξ U φ hφe
    change (MorphismProperty.inverseImage _ _).relative _ (φ ≫ pullback.fst ξ f.hom) at h
    rw [← hu] at h
    exact (Space.relative_etale_uliftYoneda_map_iff B S hS u).mp h
  have hsx : (uliftYoneda.{u + 1}).map t ≫ ξ = uliftYonedaEquiv.symm x ≫ f.hom := by
    apply uliftYonedaEquiv.injective
    rw [uliftYonedaEquiv_comp, uliftYonedaEquiv_comp, Equiv.apply_symm_apply, hx]
    simp [ξ, uliftYonedaEquiv]
  let s : (uliftYoneda.{u + 1}).obj V ⟶ pullback ξ f.hom := pullback.lift _ _ hsx
  obtain ⟨w⟩ : Nonempty (C.obj U) := by
    obtain ⟨v⟩ := hV
    obtain ⟨w, -⟩ := (hφs.property s _ _ (hφs.rep.isPullback s) :
      Surjective (C.map (hφs.rep.snd s))).surj v
    obtain ⟨g, -⟩ := (ULiftYoneda.fullyFaithful.{u + 1} (C := BigFppfOver B S hS)).map_surjective
      (hφs.rep.fst s)
    exact ⟨C.map g w⟩
  obtain ⟨Iu, K, hKF, hKA, hKfin, hKsep, e, he⟩ :=
    (etale_iff_iso_coproduct_spectra_finite_separable k
      (show C.obj U ⟶ Spec (.of k) from C.map u)).mp huet
  let i : Iu := ((sigmaMk (fun i => Spec (.of (K i)))).symm (e.hom w)).1
  let v : Spec (.of (K i)) ⟶ C.obj U := Sigma.ι (fun i => Spec (.of (K i))) i ≫ e.inv
  have hv : v ≫ C.map u = Spec.map (CommRingCat.ofHom (algebraMap k (K i))) := by
    change (Sigma.ι (fun i => Spec (.of (K i))) i ≫ e.inv) ≫
      (show C.obj U ⟶ Spec (.of k) from C.map u) = _
    rw [Category.assoc, ← he, e.inv_hom_id_assoc, Sigma.ι_comp_desc]
  have hL : B.Contains (Spec (.of (K i))) :=
    Scheme.size_Spec_lt_of_finiteType B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
      k (K i) hk
  let Lo := (specOver (hS := hS) hL (Spec.map (CommRingCat.ofHom (algebraMap k (K i))) ≫ pk)).1
  let j : Lo ⟶ T₀ := Over.homMk (ObjectProperty.homMk
    (Spec.map (CommRingCat.ofHom (algebraMap k (K i))))) (by rfl)
  let v' : Lo ⟶ U := Over.homMk (ObjectProperty.homMk v) (by
    apply ObjectProperty.hom_ext
    change v ≫ U.hom.hom = _
    have ht := congrArg (fun z => z.hom) u.w
    change C.map u ≫ pk = U.hom.hom at ht
    rw [← ht]
    exact (reassoc_of% hv) pk)
  have hv' : v' ≫ u = j := Over.OverMorphism.ext (ObjectProperty.hom_ext _ hv)
  refine ⟨K i, hKF i, hKA i, hKfin i, hKsep i, hL,
    uliftYonedaEquiv ((uliftYoneda.{u + 1}).map v' ≫ φ ≫ pullback.snd ξ f.hom), ?_⟩
  have h1 : ((uliftYoneda.{u + 1}).map v' ≫ φ ≫ pullback.snd ξ f.hom) ≫ f.hom =
      (uliftYoneda.{u + 1}).map j ≫ ξ := by
    rw [Category.assoc, Category.assoc, ← pullback.condition, ← Category.assoc φ, ← hu,
      ← Category.assoc, ← Functor.map_comp, hv']
  rw [← uliftYonedaEquiv_comp, h1]
  exact ((uliftYonedaEquiv_naturality ξ j.op).trans (by rfl)).symm.trans
    (congrArg (Y.obj.map j.op) (Equiv.apply_symm_apply _ y))

end ResiduePoint

section EtaleLift

open _root_.Polynomial
open scoped _root_.Polynomial

/-- **A finite separable extension of a residue field lifts to an étale algebra.** Let
`π : R →+* k` be a surjection onto a field and `L` a finite separable extension of `k`, with
primitive element the generator of `Field.powerBasisOfFiniteOfSeparable`. A monic lift `G` of
its minimal polynomial defines the standard étale `R`-algebra `R[X]_{G'} ⧸ (G)`, whose element
`X` is a root of `G`, and whose reduction modulo the kernel of `π` is nonzero, since it maps
onto `L`. -/
theorem exists_etale_root_of_finite_separable (R : Type u) [CommRing R] (k : Type u) [Field k]
    (π : R →+* k) (hπ : Function.Surjective π) (L : Type u) [Field L] [Algebra k L]
    [Module.Finite k L] [Algebra.IsSeparable k L] :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (a : A)
      (G : R[X]), aeval a G = 0 ∧
        G.map π = minpoly k (Field.powerBasisOfFiniteOfSeparable k L).gen ∧
        (RingHom.ker π).map (algebraMap R A) ≠ ⊤ := by
  classical
  set pb := Field.powerBasisOfFiniteOfSeparable k L
  set g := minpoly k pb.gen
  have hgmon : g.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral pb.gen)
  obtain ⟨G₀, hG₀⟩ := Polynomial.map_surjective π hπ g
  obtain ⟨G, hG, -, hGm⟩ := Polynomial.lifts_and_degree_eq_and_monic
    ((Polynomial.mem_lifts g).mpr ⟨G₀, hG₀⟩) hgmon
  let P : StandardEtalePair R := ⟨G, hGm, derivative G, ⟨1, 0, 1, by ring⟩⟩
  let : Algebra R k := π.toAlgebra
  let : Algebra R L := ((algebraMap k L).comp π).toAlgebra
  have : IsScalarTower R k L := IsScalarTower.of_algebraMap_eq fun r => rfl
  have haeval : ∀ q : R[X], aeval pb.gen q = aeval pb.gen (q.map π) :=
    fun q => (Polynomial.aeval_map_algebraMap k pb.gen q).symm
  have hmap : P.HasMap pb.gen := by
    refine ⟨?_, ?_⟩
    · change aeval pb.gen G = 0
      rw [haeval, hG]
      exact minpoly.aeval _ _
    · change IsUnit (aeval pb.gen (derivative G))
      rw [haeval, ← Polynomial.derivative_map, hG]
      exact (Polynomial.Separable.aeval_derivative_ne_zero
        (Algebra.IsSeparable.isSeparable k pb.gen) (minpoly.aeval _ _)).isUnit
  refine ⟨P.Ring, inferInstance, inferInstance, inferInstance, P.X, G, P.hasMap_X.1, hG,
    fun htop => ?_⟩
  have h1 : ((RingHom.ker π).map (algebraMap R P.Ring)).map
      (P.lift pb.gen hmap).toRingHom = ⊤ := by
    rw [htop, Ideal.map_top]
  have hc : (P.lift pb.gen hmap).toRingHom.comp (algebraMap R P.Ring) = algebraMap R L :=
    (P.lift pb.gen hmap).comp_algebraMap
  have h2 : (RingHom.ker π).map (algebraMap R L) = ⊥ := by
    rw [eq_bot_iff, Ideal.map_le_iff_le_comap]
    intro r hr
    change algebraMap k L (π r) = 0
    rw [RingHom.mem_ker.mp hr, map_zero]
  rw [Ideal.map_map, hc, h2] at h1
  exact bot_ne_top h1

end EtaleLift

section Lift

open Cardinal

/-- A weak ideal of definition of a topological local ring whose maximal ideal is open lies in
the maximal ideal: its elements are topologically nilpotent, so some power of each lies in the
maximal ideal, which is prime. -/
theorem weakIdeal_le_maximalIdeal {R : Type u} [CommRing R] [IsLocalRing R] [TopologicalSpace R]
    (hm : IsOpen ((IsLocalRing.maximalIdeal R : Ideal R) : Set R))
    (J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I }) :
    J.1 ≤ IsLocalRing.maximalIdeal R := by
  intro x hx
  obtain ⟨n, hn⟩ := ((J.2.2 x hx).eventually (hm.mem_nhds (Ideal.zero_mem _))).exists
  exact (IsLocalRing.maximalIdeal.isMaximal R).isPrime.mem_of_pow_mem n hn

/-- The residue field stage of the formal spectrum of a local ring with the adic topology. -/
abbrev residueStage {R : Type u} [CommRing R] [IsLocalRing R] [TopologicalSpace R]
    [IsTopologicalRing R] (hRadic : _root_.IsAdic (IsLocalRing.maximalIdeal R)) :
    { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I } :=
  ⟨IsLocalRing.maximalIdeal R, TopologicalRing.isWeakIdealOfDefinition_of_isAdic hRadic⟩

/-- The morphism of field spectra over `S` from a field extension `L` of the residue field of
`R` to the residue field stage of a quotient system of `R`. -/
abbrev residueStageMap {R : Type u} [CommRing R] [IsLocalRing R] [TopologicalSpace R]
    [IsTopologicalRing R] (hRadic : _root_.IsAdic (IsLocalRing.maximalIdeal R))
    (D : QuotientSystem B S hS R) (L : Type u) [Field L]
    [Algebra (IsLocalRing.ResidueField R) L] (hL : B.Contains (Spec (.of L))) :
    (specOver (hS := hS) hL (Spec.map (CommRingCat.ofHom
        (algebraMap (IsLocalRing.ResidueField R) L)) ≫ D.overS (residueStage hRadic))).1 ⟶
      (BigAffineFppf.inclusion B S hS).obj (D.stage (residueStage hRadic)) :=
  Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom
    (algebraMap (IsLocalRing.ResidueField R) L)))) (by rfl)

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- **A point of the fibre product over an adic point yields a finite separable point over the
residue field.** Let `f : X ⟶ Y` be representable by algebraic spaces and étale and let
`p : Spf R ⟶ Y` be a morphism out of the formal spectrum of a local ring with the adic topology
of its maximal ideal. A point of `Spf R ×_Y X` produces a finite separable extension `L` of
the residue field `κ` of `R` and a section of `X` over `Spec L` lying over the restriction of
`p` to `Spec L ⟶ Spec κ`.

The point is a section over the spectrum of a field `K`; its image in `Spf R` factors through a
quotient stage (Stacks 0AIF), hence through `Spec κ`, since the weak ideals of definition lie
in the maximal ideal and `K` is reduced. Then
`exists_finite_separable_section_of_isRepresentableEtale` applies. -/
theorem exists_finite_separable_section_of_pointsULift_pullback {X Y : FppfSheaf B S hS}
    (f : X ⟶ Y) (hf : IsRepresentableEtale B S hS f)
    {R : Type u} [CommRing R] [IsLocalRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsLinearTopology R R]
    (hRadic : _root_.IsAdic (IsLocalRing.maximalIdeal R))
    (_hRweak : TopologicalRing.IsWeaklyAdmissible R)
    (D : QuotientSystem B S hS R) (p : formalSpectrum D ⟶ Y)
    (zZ : Space.pointsULift.{u + 1} B S hS (pullback p f).obj) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra (IsLocalRing.ResidueField R) L)
      (_ : Module.Finite (IsLocalRing.ResidueField R) L)
      (_ : Algebra.IsSeparable (IsLocalRing.ResidueField R) L)
      (hL : B.Contains (Spec (.of L)))
      (bL : X.obj.obj (op (specOver (hS := hS) hL (Spec.map (CommRingCat.ofHom
        (algebraMap (IsLocalRing.ResidueField R) L)) ≫ D.overS (residueStage hRadic))).1)),
      f.hom.app _ bL = Y.obj.map (residueStageMap hRadic D L hL).op
        (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)
          (formalSpectrumInclusion D (OrderDual.toDual (residueStage hRadic)) ≫ p)) := by
  classical
  obtain ⟨z₀, rfl⟩ := Quot.exists_rep zZ
  let Kobj := z₀.siteObject B S hS (pullback p f).obj
  let vK : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj Kobj ⟶ pullback p f :=
    (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).symm z₀.value
  let a := vK ≫ pullback.fst p f
  let b := vK ≫ pullback.snd p f
  have hab : b ≫ f = a ≫ p := by
    simp only [a, b, Category.assoc, pullback.condition]
  let Kaff : BigAffineFppf B S hS := ⟨Kobj, inferInstanceAs (IsAffine (Spec (.of z₀.carrier)))⟩
  have : Nonempty (OrderDual { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I }) :=
    ⟨OrderDual.toDual (adicStage hRadic 0)⟩
  have : IsDirected (OrderDual { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I })
      (· ≤ ·) := TopologicalRing.isDirected_weakIdealOfDefinitionIndex R
  obtain ⟨j, g, hg⟩ := exists_factor_to_affine_stage B S hS (formalSpectrum D)
    (OrderDual { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I }) D.diagram
    (fun _ _ φ => D.isThickening_map_diagram φ) (Iso.refl _) Kaff a
  let Jm := residueStage hRadic
  let jj := OrderDual.ofDual j
  have hjm : jj.1 ≤ Jm.1 :=
    weakIdeal_le_maximalIdeal (by simpa using (isAdic_iff.mp hRadic).1 1) _
  let gs : Spec (.of z₀.carrier) ⟶ Spec (.of (R ⧸ jj.1)) :=
    (BigAffineFppf.toScheme B S hS).map g
  let φ : R ⧸ jj.1 →+* z₀.carrier := (Spec.preimage gs).hom
  have hφ : ∀ r ∈ Jm.1, φ (Ideal.Quotient.mk _ r) = 0 := by
    intro r hr
    obtain ⟨n, hn⟩ := (isAdic_iff.mp hRadic).2 _ (jj.2.1.mem_nhds (Ideal.zero_mem _))
    exact IsNilpotent.eq_zero ⟨n, by rw [← map_pow, ← map_pow,
      Ideal.Quotient.eq_zero_iff_mem.mpr (hn (Ideal.pow_mem_pow hr n)), map_zero]⟩
  let : Field (R ⧸ Jm.1) := Ideal.Quotient.field _
  let ψ : R ⧸ Jm.1 →+* z₀.carrier :=
    Ideal.Quotient.lift _ (φ.comp (Ideal.Quotient.mk _)) hφ
  have hψ : ψ.comp (Ideal.Quotient.factor hjm) = φ := by ext; rfl
  have hgs : Spec.map (CommRingCat.ofHom ψ) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hjm)) = gs := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ]
    exact Spec.map_preimage gs
  let Tm := (BigAffineFppf.inclusion B S hS).obj (D.stage Jm)
  let t : Kobj ⟶ Tm := Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom ψ))) (by
    apply ObjectProperty.hom_ext
    have hw := congrArg (fun z => z.hom) g.hom.w
    change gs ≫ D.overS jj = z₀.toBase at hw
    change Spec.map (CommRingCat.ofHom ψ) ≫ D.overS Jm = z₀.toBase
    rw [← D.compatible jj Jm hjm, ← Category.assoc, hgs, hw])
  have hgt : (BigAffineFppf.inclusion B S hS).map g =
      t ≫ (BigAffineFppf.inclusion B S hS).map (D.transition hjm) :=
    Over.OverMorphism.ext (ObjectProperty.hom_ext _ hgs.symm)
  have ha : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map t ≫
      formalSpectrumInclusion D (OrderDual.toDual Jm) = a := by
    refine (congrArg (fun c => (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map t ≫ c)
      (colimit.w (formalSpectrumDiagram D) (homOfLE hjm : OrderDual.toDual Jm ⟶ j)).symm).trans
        ((Category.assoc _ _ _).symm.trans ?_)
    refine (congrArg (fun c => c ≫ colimit.ι (formalSpectrumDiagram D) j)
      (((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map_comp _ _).symm.trans
        (congrArg (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map hgt.symm))).trans ?_
    exact Eq.trans (congrArg _ (Category.comp_id _).symm) hg
  let y₀ : Y.obj.obj (op Tm) :=
    Sheaf.sectionEquiv (BigFppfOver.topology B S hS)
      (formalSpectrumInclusion D (OrderDual.toDual Jm) ≫ p)
  have hx : f.hom.app (op Kobj) (Sheaf.sectionEquiv (BigFppfOver.topology B S hS) b) =
      Y.obj.map t.op y₀ :=
    (Sheaf.sectionEquiv_comp _ b f).symm.trans ((congrArg _ hab).trans
      (sectionEquiv_comp_eq_map t ha p))
  exact exists_finite_separable_section_of_isRepresentableEtale f hf (R ⧸ Jm.1) (D.inSite Jm)
    (D.overS Jm) y₀ Kobj (inferInstanceAs (Nonempty (Spec (.of z₀.carrier)))) t
    (Sheaf.sectionEquiv (BigFppfOver.topology B S hS) b) hx

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- **The lifting step of Stacks 0AQU, from a point of the fibre product.** Let `f : X ⟶ Y`
be a morphism of fppf sheaves over `S` which is representable by algebraic spaces and étale,
and let `p : Spf R ⟶ Y` be a morphism out of the formal spectrum of a discrete valuation ring
with the adic topology. Then a point of `Spf R ×_Y X` produces the lift that the definition of
rig-surjectivity asks for: an extension `R ⊂ R'` of complete discrete valuation rings and a
morphism `Spf R' ⟶ X` over `p`.

The point gives a section of `X` over `Spec L` for a finite separable extension `L` of the
residue field `κ` of `R`, lying over `p`
(`exists_finite_separable_section_of_pointsULift_pullback`). A monic lift of the minimal
polynomial of a primitive element of `L` defines an étale `R`-algebra `A` with
`A ⧸ 𝔪_R A ≠ 0` (`exists_etale_root_of_finite_separable`), which maps to a complete discrete
valuation ring extension `R ⊂ R'` (Stacks 00PH and Stacks 0AP1, through
`exists_isAdicComplete_isDiscreteValuationRing_of_etale`). The image of the root in
`R' ⧸ 𝔪_{R'}` embeds `L` over `κ`, which maps the closed stage of `Spf R'` to `X` over `p`.
Finally `f` is formally étale (`formallyEtale_hom_of_isRepresentableEtale`), so that map extends
to `Spf R'` along the tower of square-zero thickenings of its stages
(`exists_lift_formalSpectrum_of_formallyEtale`).

This is the source's argument with the order of two steps exchanged: the source first takes an
affine étale chart of the fibre product, which needs the fibre product to be a formal algebraic
space (Stacks 0AJ3, hence Stacks 0AIU), and then reads off the étale algebra by Stacks 0AN8.
Here the étale algebra is built from the point directly and the chart is never formed. -/
theorem exists_lift_of_pointsULift_pullback_of_isRepresentableEtale {X Y : FppfSheaf B S hS}
    (f : X ⟶ Y) (hf : IsRepresentableEtale B S hS f)
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsLinearTopology R R]
    (hRadic : _root_.IsAdic (IsLocalRing.maximalIdeal R))
    (hRweak : TopologicalRing.IsWeaklyAdmissible R) (hRcard : #R < B.cutoff)
    (D : QuotientSystem B S hS R) (p : formalSpectrum D ⟶ Y)
    (zZ : Space.pointsULift.{u + 1} B S hS (pullback p f).obj) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : IsDiscreteValuationRing R')
      (_ : Algebra R R') (_ : IsDiscreteValuationRing.IsExtension R R')
      (_ : TopologicalSpace R') (_ : IsTopologicalRing R') (_ : IsLinearTopology R' R'),
      _root_.IsAdic (IsLocalRing.maximalIdeal R') ∧
        IsAdicComplete (IsLocalRing.maximalIdeal R') R' ∧
          ∃ (D' : QuotientSystem B S hS R') (e : ContinuousHom D D')
            (x : formalSpectrum D' ⟶ X),
            e.toRingHom = algebraMap R R' ∧ x ≫ f = formalSpectrumMap hRweak e ≫ p := by
  classical
  obtain ⟨L, hLF, hLA, hLfin, hLsep, hL, bL, hbL⟩ :=
    exists_finite_separable_section_of_pointsULift_pullback f hf hRadic hRweak D p zZ
  obtain ⟨A, hAring, hAalg, hAet, a₀, G, haG, hGmap, hAker⟩ :=
    exists_etale_root_of_finite_separable R (IsLocalRing.ResidueField R)
      (IsLocalRing.residue R) IsLocalRing.residue_surjective L
  have hAcard : #A < B.cutoff :=
    (Cardinal.mk_le_max_aleph0_of_finiteType R A).trans_lt
      (max_lt B.aleph0_lt_cutoff hRcard)
  obtain ⟨W, hWring, hWdom, hWdvr, hRW, hWext, hWcomplete, gW, hgcomp, hWcard⟩ :=
    exists_isAdicComplete_isDiscreteValuationRing_of_etale R A
      (by rwa [IsLocalRing.ker_residue] at hAker) B.cutoff
      B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit hAcard
  let : TopologicalSpace W := (IsLocalRing.maximalIdeal W).adicTopology
  have hWtopring : IsTopologicalRing W :=
    (IsLocalRing.maximalIdeal W).ringFilterBasis.isTopologicalRing
  have hWlin : IsLinearTopology W W := (IsLocalRing.maximalIdeal W).isLinearTopology
  have hWadic : _root_.IsAdic (IsLocalRing.maximalIdeal W) := rfl
  have hmle : (IsLocalRing.maximalIdeal R).map (algebraMap R W) ≤
      IsLocalRing.maximalIdeal W :=
    Ideal.map_le_iff_le_comap.mpr (by rw [IsLocalRing.maximalIdeal_comap])
  obtain ⟨DW, e, he⟩ := exists_quotientSystem_continuousHom hRweak D (algebraMap R W)
    (continuous_of_isAdic_of_map_le hRadic hWadic _ hmle) hWcard
  let KW := adicStage hWadic 0
  have hKW : KW.1 = IsLocalRing.maximalIdeal W := by simp [KW, adicStage]
  have hmKW : (residueStage hRadic).1 ≤ Ideal.comap e.toRingHom KW.1 := by
    rw [he, hKW]
    exact Ideal.map_le_iff_le_comap.mp hmle
  let ρ : IsLocalRing.ResidueField R →+* W ⧸ KW.1 := Ideal.quotientMap KW.1 e.toRingHom hmKW
  let : Algebra (IsLocalRing.ResidueField R) (W ⧸ KW.1) := ρ.toAlgebra
  let w : W ⧸ KW.1 := Ideal.Quotient.mk KW.1 (gW a₀)
  have hw : Polynomial.aeval w (minpoly (IsLocalRing.ResidueField R)
      (Field.powerBasisOfFiniteOfSeparable (IsLocalRing.ResidueField R) L).gen) = 0 := by
    have hc : ρ.comp (IsLocalRing.residue R) =
        ((Ideal.Quotient.mk KW.1).comp gW).comp (algebraMap R A) := by
      ext r
      change Ideal.Quotient.mk KW.1 (e.toRingHom r) = Ideal.Quotient.mk KW.1 (gW (algebraMap R A r))
      rw [he, ← RingHom.comp_apply gW, hgcomp]
    rw [← hGmap, Polynomial.aeval_def, Polynomial.eval₂_map]
    change Polynomial.eval₂ (ρ.comp (IsLocalRing.residue R)) w G = 0
    rw [hc, show w = ((Ideal.Quotient.mk KW.1).comp gW) a₀ from rfl, ← Polynomial.hom_eval₂,
      ← Polynomial.aeval_def, haG, map_zero]
  let μr : L →ₐ[IsLocalRing.ResidueField R] W ⧸ KW.1 :=
    (Field.powerBasisOfFiniteOfSeparable (IsLocalRing.ResidueField R) L).lift w hw
  have hμr : μr.toRingHom.comp (algebraMap (IsLocalRing.ResidueField R) L) =
      Ideal.quotientMap KW.1 e.toRingHom hmKW :=
    μr.comp_algebraMap
  have hsp : Spec.map (CommRingCat.ofHom μr.toRingHom) ≫ Spec.map (CommRingCat.ofHom
      (algebraMap (IsLocalRing.ResidueField R) L)) =
        Spec.map (CommRingCat.ofHom (Ideal.quotientMap KW.1 e.toRingHom hmKW)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hμr]
    rfl
  let μ : (BigAffineFppf.inclusion B S hS).obj (DW.stage KW) ⟶
      (specOver (hS := hS) hL (Spec.map (CommRingCat.ofHom
        (algebraMap (IsLocalRing.ResidueField R) L)) ≫ D.overS (residueStage hRadic))).1 :=
    Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom μr.toRingHom)))
      (ObjectProperty.hom_ext _ (((reassoc_of% hsp) _).trans
        (e.overS (residueStage hRadic) KW hmKW)))
  have hμ : μ ≫ residueStageMap hRadic D L hL =
      (BigAffineFppf.inclusion B S hS).map (e.stageMap (residueStage hRadic) KW hmKW) :=
    Over.OverMorphism.ext (ObjectProperty.hom_ext _ hsp)
  let z₀ : (formalSpectrumDiagram DW).obj (OrderDual.toDual KW) ⟶ X :=
    (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).symm (X.obj.map μ.op bL)
  have hz₀ : z₀ ≫ f = formalSpectrumInclusion DW (OrderDual.toDual KW) ≫
      (formalSpectrumMap hRweak e ≫ p) := by
    apply (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).injective
    have hRHS := (congrArg (Sheaf.sectionEquiv (BigFppfOver.topology B S hS))
      (Category.assoc _ _ p)).trans (sectionEquiv_comp_eq_map
        ((BigAffineFppf.inclusion B S hS).map (e.stageMap (residueStage hRadic) KW hmKW))
        (formalSpectrumMap_spec hRweak e (residueStage hRadic) KW hmKW).symm p)
    refine (Sheaf.sectionEquiv_comp _ z₀ f).trans (Eq.trans ?_ hRHS.symm)
    have hz : Sheaf.sectionEquiv (BigFppfOver.topology B S hS) z₀ = X.obj.map μ.op bL :=
      Equiv.apply_symm_apply _ _
    rw [hz]
    refine (NatTrans.naturality_apply f.hom μ.op bL).trans ?_
    rw [hbL, ← Functor.map_comp_apply, ← op_comp, hμ]
  obtain ⟨x, hx⟩ := exists_lift_formalSpectrum_of_formallyEtale f
    (formallyEtale_hom_of_isRepresentableEtale f hf) hWadic DW
    (formalSpectrumMap hRweak e ≫ p) z₀ hz₀
  exact ⟨W, hWring, hWdom, hWdvr, hRW, hWext, inferInstance, hWtopring, hWlin, hWadic,
    hWcomplete, DW, e, x, he, hx⟩

/-- The closed point of the formal spectrum of a local ring with the adic topology: the
quotient stage of the maximal ideal is the spectrum of the residue field, a field spectrum of
the site, and its inclusion into the formal spectrum is a section over it. -/
noncomputable def residuePoint {R : Type u} [CommRing R] [IsLocalRing R] [TopologicalSpace R]
    [IsTopologicalRing R] (hRadic : _root_.IsAdic (IsLocalRing.maximalIdeal R))
    (D : QuotientSystem B S hS R) :
    Space.FieldValuedPointULift.{u + 1} B S hS (formalSpectrum D).obj :=
  letI : Field (R ⧸ (residueStage hRadic).1) := Ideal.Quotient.field _
  { carrier := R ⧸ (residueStage hRadic).1
    contained := D.inSite (residueStage hRadic)
    toBase := D.overS (residueStage hRadic)
    value := Sheaf.sectionEquiv (BigFppfOver.topology B S hS)
      (formalSpectrumInclusion D (OrderDual.toDual (residueStage hRadic))) }

/-- **Stacks 0AQU.** A morphism of fppf sheaves over `S` which is representable by algebraic
spaces, étale and surjective is rig-surjective.

Let `p : Spf R ⟶ Y` be an adic morphism out of the formal spectrum of a complete discrete
valuation ring. The closed point of `Spf R` maps to a point of `Y`, which by surjectivity is
the image of a point of `X`; together they give a point of `Spf R ×_Y X`
(`AlgebraicGeometry.Space.exists_point_of_isPullbackULift`), and
`exists_lift_of_pointsULift_pullback_of_isRepresentableEtale` turns that point into the lift
the definition of rig-surjectivity asks for.

The source states this for locally Noetherian formal algebraic spaces `X` and `Y`; neither
hypothesis is used, so neither is assumed. Nor is adicness of `p`: the lift exists for every
morphism out of the formal spectrum of a complete discrete valuation ring. -/
@[stacks 0AQU]
theorem isRigSurjective_of_isSurjective_of_isRepresentableEtale {X Y : FppfSheaf B S hS}
    (f : X ⟶ Y) (hf : IsRepresentableEtale B S hS f) (hsurj : IsSurjective B S hS f) :
    IsRigSurjective B S hS f := by
  classical
  intro R _ _ _ _ _ _ hRadic hRcomplete hRweak D p _
  have hRcard : #R < B.cutoff := mk_lt_cutoff_of_quotientSystem hRadic hRcomplete D
  let zpt := (residuePoint hRadic D).class B S hS (formalSpectrum D).obj
  obtain ⟨xpt, hxpt⟩ :=
    hsurj (Space.pointsMapULift.{u + 1} B S hS (formalSpectrum D).obj p.hom zpt)
  obtain ⟨zZ, -, -⟩ := Space.exists_point_of_isPullbackULift B S hS
    ((IsPullback.of_hasPullback p f).map
      (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))) zpt xpt hxpt.symm
  exact exists_lift_of_pointsULift_pullback_of_isRepresentableEtale f hf hRadic hRweak
    hRcard D p zZ

end Lift

end AlgebraicGeometry.FormalSpace

end
