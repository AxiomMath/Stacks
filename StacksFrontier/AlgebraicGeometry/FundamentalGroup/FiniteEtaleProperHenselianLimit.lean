module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleAlgClosedExtension
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleOverLimit
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProperEquivalence
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProperGRing
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FiniteAlgebraization.Existence
public import StacksFrontier.AlgebraicGeometry.Limits.ProperLimitOfFiniteTypeOverZ
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.IsomorphismApproximationComplete
public import StacksFrontier.RingTheory.GRing.EssFiniteType
public import StacksFrontier.RingTheory.GRing.Henselization
public import StacksFrontier.RingTheory.Henselian.Henselization.Basic
public import StacksFrontier.RingTheory.Henselian.HenselizationUniversalProperty
import all StacksFrontier.AlgebraicGeometry.Fibres.IdempotentExtensionApproximation

/-!
# Tag 0A48 over an arbitrary henselian local ring, from the case of a G-ring

The proof of [Stacks, Tag 0A48] proceeds in stages: a complete local Noetherian ring, then a
henselian local Noetherian G-ring, then an arbitrary henselian local ring. This file carries out
the last stage ("General case" in the source): the conclusion of Tag 0A48 for every henselian
local ring, `AlgebraicGeometry.ProperHenselianFiniteEtaleEquivalence`, follows from its
restriction to henselian local Noetherian G-rings.

## Main results

* `AlgebraicGeometry.isEquivalence_finiteEtaleBaseChange_of_isProper_of_henselianLocalRing`:
  **Tag 0A48**, unconditionally, and `AlgebraicGeometry.properHenselianFiniteEtaleEquivalence`,
  the same in the shape `ProperHenselianFiniteEtaleEquivalence`.
* `AlgebraicGeometry.properHenselianFiniteEtaleEquivalence_of_adicFiniteAlgebraAlgebraization`: the
  three stages composed -- Tag 0A48 for all henselian local rings, granted Grothendieck existence
  for finite sheaves of algebras over complete local Noetherian rings.
* `AlgebraicGeometry.properHenselianFiniteEtaleEquivalence_of_isGRing`: Tag 0A48 for all henselian
  local rings, granted Tag 0A48 for henselian local Noetherian G-rings.
* `AlgebraicGeometry.isEquivalence_finiteEtaleBaseChange_closedFibre_of_isGRing`: the same for one
  henselian local ring and one proper scheme over it.
* `AlgebraicGeometry.essSurj_finiteEtaleBaseChange_fiber_closedPoint_of_isGRing`: essential
  surjectivity onto the fibre over the closed point, which is where the limit argument happens.
* `AlgebraicGeometry.essSurj_finiteEtaleBaseChange_of_isLimit_of_factors`: base change to the limit
  of a cofiltered system is essentially surjective on finite étale covers if, at every stage, the
  projection factors through a base change which is.
* `AlgebraicGeometry.isGRing_stalk_of_locallyOfFiniteType_terminal`: the local rings of a scheme
  locally of finite type over `ℤ` are G-rings (Tag 07PX).

## Implementation notes

The source writes `p : X ⟶ Spec A` as the limit of proper `Xᵢ ⟶ Sᵢ` with `Sᵢ` of finite type over
`ℤ` (Tag 0A0P), sets `Aᵢ = 𝒪_{Sᵢ,sᵢ}`, observes `A = colim Aᵢʰ` (Tags 07PX, 0A04, 07QR), so that
`X = lim Xᵢ ×_{Sᵢ} Spec Aᵢʰ` with closed fibre the limit of the closed fibres, and deduces the
result from the case of the G-rings `Aᵢʰ` by the description of finite étale covers of a limit
(Tags 01ZM, 01ZO, 07RP).

Only essential surjectivity is proved by that argument here: full faithfulness is reduced to
essential surjectivity (for the schemes finite étale over `X`) by
`isEquivalence_finiteEtaleBaseChange_of_isProper_of_henselianPair_of_essSurj`. For essential
surjectivity the colimit `A = colim Aᵢʰ` is not needed in full: it suffices that the fibre `X_s`
of `p` over the closed point is the limit of the fibres `(Xᵢ)_{sᵢ}`
(`Stacks.AlgebraicGeometry.Fibres.fiberConeIsLimit`, which rests on the residue-field colimit of
Tag 0CUG), so that a finite étale cover of `X_s` comes from some `(Xᵢ)_{sᵢ}`
(`exists_finiteEtale_model`), and that at each stage `X_s ⟶ (Xᵢ)_{sᵢ}` factors through the closed
fibre of `Yᵢ = Xᵢ ×_{Sᵢ} Spec Aᵢʰ` compatibly with a map `X ⟶ Yᵢ`. That map comes from the local
homomorphism `Aᵢʰ ⟶ A` given by the universal property of the henselization (Tag 04GS) applied to
`Aᵢ ⟶ A`, and the factorization is
`exists_factorization_fiber_closedPoint_of_isGRing`. The hypothesis, applied to the proper
`Yᵢ ⟶ Spec Aᵢʰ` over the henselian local Noetherian G-ring `Aᵢʰ`, lifts the cover of the closed
fibre of `Yᵢ` to `Yᵢ`, and its pullback to `X` is the required cover.

The fibre over the closed point is `X ×_{Spec A} Spec κ(s)`, built from
`Scheme.fromSpecResidueField`, while the closed fibre in `ProperHenselianFiniteEtaleEquivalence` is
`X ×_{Spec A} Spec (A/𝔪)`; `essSurj_finiteEtaleBaseChange_closedFibre_of_fiber` moves between them.
The closed point is passed as a variable `s` with `hs : s = closedPoint _`: the term
`(Spec (.of A)).residueField (closedPoint _)` is not type-correct at `implicit` transparency, which
defeats `rw` and `simp`.

The fibre-of-a-limit construction of
`StacksFrontier.AlgebraicGeometry.Fibres.IdempotentExtensionApproximation` (`fiberDiagram`,
`fiberCone`, `fiberConeIsLimit`, `residueSpecConeIsLimit`, and the arrow-cone limits
`isLimitLeftFuncMapCone`, `isLimitRightFuncMapCone`) is private to that module; it is reached
here by `import all`, and the three instance facts about the stages of the diagram of fibres that
its proof of Tag 0G7X establishes inline are restated here as private lemmas.

The hypothesis is stated inline as the restriction of `ProperHenselianFiniteEtaleEquivalence` to
henselian local rings that are G-rings (a G-ring is Noetherian by definition, `IsGRing`).

## References

* [Stacks Project, Tag 0A48](https://stacks.math.columbia.edu/tag/0A48)
* [Stacks Project, Tag 0A0P](https://stacks.math.columbia.edu/tag/0A0P)
* [Stacks Project, Tag 07PX](https://stacks.math.columbia.edu/tag/07PX)
* [Stacks Project, Tag 07QR](https://stacks.math.columbia.edu/tag/07QR)
* [Stacks Project, Tag 0A04](https://stacks.math.columbia.edu/tag/0A04)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 01ZO](https://stacks.math.columbia.edu/tag/01ZO)
* [Stacks Project, Tag 07RP](https://stacks.math.columbia.edu/tag/07RP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing

universe u

/-! ### The stages of the diagram of fibres -/

namespace Stacks.AlgebraicGeometry.Fibres

open _root_.AlgebraicGeometry

/-- **The transition morphisms of the diagram of fibres are affine** as soon as those of the
diagrams of sources and of targets are, by `isAffineHom_pullback_map`. -/
private lemma isAffineHom_fiberDiagram_map {J : Type u} [Category.{u} J] {A B : J ⥤ Scheme.{u}}
    (φ : A ⟶ B) (cB : Cone B) (s : cB.pt) [∀ {i j : J} (g : i ⟶ j), IsAffineHom (A.map g)]
    [∀ {i j : J} (g : i ⟶ j), IsAffineHom (B.map g)] {i j : J} (g : i ⟶ j) :
    IsAffineHom ((fiberDiagram φ cB s).map g) :=
  isAffineHom_pullback_map _ _ _ _ (A.map g) (Spec.map (residueTransition B cB s g)) (B.map g)
    (φ.naturality g).symm (specMap_residueTransition B cB s g).symm

/-- **The stages of the diagram of fibres are quasi-compact** when the components of `φ` are:
each is quasi-compact over the spectrum of a field. -/
private lemma compactSpace_fiberDiagram_obj {J : Type u} [Category.{u} J] {A B : J ⥤ Scheme.{u}}
    (φ : A ⟶ B) (cB : Cone B) (s : cB.pt) [∀ j, QuasiCompact (φ.app j)] (j : J) :
    CompactSpace ((fiberDiagram φ cB s).obj j) :=
  (quasiCompact_iff_compactSpace (pullback.snd (φ.app j)
    ((B.obj j).fromSpecResidueField (cB.π.app j s)))).mp inferInstance

/-- **The stages of the diagram of fibres are quasi-separated** when the components of `φ` are:
each is quasi-separated over the spectrum of a field. -/
private lemma quasiSeparatedSpace_fiberDiagram_obj {J : Type u} [Category.{u} J]
    {A B : J ⥤ Scheme.{u}} (φ : A ⟶ B) (cB : Cone B) (s : cB.pt)
    [∀ j, QuasiSeparated (φ.app j)] (j : J) :
    QuasiSeparatedSpace ((fiberDiagram φ cB s).obj j) := by
  have hqs : QuasiSeparated (pullback.snd (φ.app j)
      ((B.obj j).fromSpecResidueField (cB.π.app j s))) :=
    MorphismProperty.of_isPullback (P := @QuasiSeparated)
      (IsPullback.of_hasPullback _ _) inferInstance
  exact quasiSeparatedSpace_of_quasiSeparated (pullback.snd (φ.app j)
    ((B.obj j).fromSpecResidueField (cB.π.app j s)))

end Stacks.AlgebraicGeometry.Fibres

namespace AlgebraicGeometry

/-- **Lifting finite étale covers through a factorization at every stage.** Let `c` be a limit of a
cofiltered system of quasi-compact quasi-separated schemes with affine transition morphisms, and
let `g : c.pt ⟶ X`. Suppose that at every stage `j` there are a morphism `X ⟶ Y`, a morphism
`r : Y₀ ⟶ Y` along which base change is essentially surjective on finite étale covers, and a
factorization `c.pt ⟶ Y₀ ⟶ D.obj j` of the projection with `c.pt ⟶ Y₀ ⟶ Y` equal to
`c.pt ⟶ X ⟶ Y`. Then base change along `g` is essentially surjective on finite étale covers.

A finite étale cover of `c.pt` comes from one of a stage (`exists_finiteEtale_model`); pulled back
to `Y₀` it is the base change of a cover of `Y`, whose pullback to `X` is the required cover. -/
theorem essSurj_finiteEtaleBaseChange_of_isLimit_of_factors {I : Type u} [Category.{u} I]
    [IsCofiltered I] (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    {X : Scheme.{u}} (g : c.pt ⟶ X)
    (h : ∀ j : I, ∃ (Y Y₀ : Scheme.{u}) (a : X ⟶ Y) (r : Y₀ ⟶ Y) (z : c.pt ⟶ Y₀)
      (w : Y₀ ⟶ D.obj j), (finiteEtaleBaseChange r).EssSurj ∧ z ≫ r = g ≫ a ∧
        z ≫ w = c.π.app j) :
    (finiteEtaleBaseChange g).EssSurj := by
  refine ⟨fun Q => ?_⟩
  obtain ⟨j, B, ⟨ε⟩⟩ := exists_finiteEtale_model D c hc Q
  obtain ⟨Y, Y₀, a, r, z, w, hr, hzr, hzw⟩ := h j
  let W := (finiteEtaleBaseChange w).obj B
  let V := (finiteEtaleBaseChange r).objPreimage W
  refine ⟨(finiteEtaleBaseChange a).obj V, ⟨?_⟩⟩
  exact (finiteEtaleBaseChangeComp g a (g ≫ a) rfl).symm.app V ≪≫
    (finiteEtaleBaseChangeComp z r (g ≫ a) hzr.symm).app V ≪≫
    (finiteEtaleBaseChange z).mapIso ((finiteEtaleBaseChange r).objObjPreimageIso W) ≪≫
    (finiteEtaleBaseChangeComp z w (c.π.app j) hzw.symm).symm.app B ≪≫ ε.symm

/-- The closed point of the spectrum of a local ring, as `Spec` of the quotient by the maximal
ideal, agrees with the spectrum of the residue field at the closed point up to an isomorphism
over `Spec A`. -/
theorem exists_isIso_comp_specMap_mk_eq_fromSpecResidueField (A : Type u) [CommRing A]
    [IsLocalRing A] (s : Spec (.of A)) (hs : s = closedPoint (CommRingCat.of A)) :
    ∃ θ : Spec ((Spec (.of A)).residueField s) ⟶ Spec (.of (A ⧸ maximalIdeal A)),
      IsIso θ ∧ θ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal A))) =
        (Spec (.of A)).fromSpecResidueField s := by
  subst hs
  let e := Scheme.Spec.residueFieldIso (CommRingCat.of A) (closedPoint (CommRingCat.of A))
  let k : CommRingCat.of (A ⧸ maximalIdeal A) ⟶
      CommRingCat.of (closedPoint (CommRingCat.of A)).asIdeal.ResidueField :=
    CommRingCat.ofHom (algebraMap (A ⧸ maximalIdeal A) (maximalIdeal A).ResidueField)
  have : IsIso k := (ConcreteCategory.isIso_iff_bijective k).2
    (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal A))
  refine ⟨Spec.map e.inv ≫ Spec.map k, inferInstance, ?_⟩
  refine (Category.assoc _ _ _).trans (Eq.trans ?_
    (Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField _ _))
  congr 1
  refine (Spec.map_comp _ _).symm.trans ?_
  congr 1

/-- Essential surjectivity of base change to the closed fibre `X ×_{Spec A} Spec (A/𝔪)` follows
from essential surjectivity of base change to the scheme-theoretic fibre over the closed point,
the two differing by an isomorphism over `X`. -/
theorem essSurj_finiteEtaleBaseChange_closedFibre_of_fiber (A : Type u) [CommRing A]
    [IsLocalRing A] {X : Scheme.{u}} (p : X ⟶ Spec (.of A))
    (h : (finiteEtaleBaseChange (pullback.fst p
      ((Spec (.of A)).fromSpecResidueField (closedPoint (CommRingCat.of A))))).EssSurj) :
    (finiteEtaleBaseChange (pullback.fst p
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal A)))))).EssSurj := by
  obtain ⟨θ, hθ, hθc⟩ := exists_isIso_comp_specMap_mk_eq_fromSpecResidueField A _ rfl
  let g := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal A)))
  have h' : (finiteEtaleBaseChange (pullback.fst p (θ ≫ g))).EssSurj := by rwa [hθc]
  let M : pullback p g ⟶ pullback p (θ ≫ g) :=
    pullback.map p g p (θ ≫ g) (𝟙 _) (inv θ) (𝟙 _) (by simp) (by simp)
  have hM : pullback.fst p g = M ≫ pullback.fst p (θ ≫ g) := by
    simp only [M, pullback.map, pullback.lift_fst, Category.comp_id]
  rw [hM]
  exact essSurj_finiteEtaleBaseChange_comp_of_isIso M _ h'

/-- **The local rings of a scheme of finite type over `ℤ` are G-rings** (Stacks 07PX): such a
local ring is essentially of finite type over a local ring of `Spec ℤ`, which is a G-ring. -/
theorem isGRing_stalk_of_locallyOfFiniteType_terminal {S : Scheme.{u}}
    [LocallyOfFiniteType (terminal.from S)] (x : S) : IsGRing (S.presheaf.stalk x) := by
  let t : ⊤_ Scheme.{u} ≅ Spec (.of (ULift.{u} ℤ)) :=
    terminalIsTerminal.uniqueUpToIso specULiftZIsTerminal
  let g : S ⟶ Spec (.of (ULift.{u} ℤ)) := terminal.from S ≫ t.hom
  have hZ : IsGRing (ULift.{u} ℤ) := by
    have hsurj : Function.Surjective (algebraMap ℤ (ULift.{u} ℤ)) := fun y =>
      ⟨y.down, by ext; simp⟩
    have : Algebra.FiniteType ℤ (ULift.{u} ℤ) :=
      RingHom.finiteType_algebraMap.mp (RingHom.FiniteType.of_surjective _ hsurj)
    exact isGRing_basic_examples.{0, u}.2.2.2.2 ℤ (ULift.{u} ℤ) isGRing_basic_examples.{0, 0}.2.2.1
  have hT := StacksDraft.ArtinApproximation.isGRing_stalk_spec (ULift.{u} ℤ) hZ (g x)
  let : Algebra ((Spec (.of (ULift.{u} ℤ))).presheaf.stalk (g x)) (S.presheaf.stalk x) :=
    (g.stalkMap x).hom.toAlgebra
  have : Algebra.EssFiniteType ((Spec (.of (ULift.{u} ℤ))).presheaf.stalk (g x))
      (S.presheaf.stalk x) := LocallyOfFiniteType.stalkMap g x
  exact isGRing_of_essFiniteType hT

/-- **The factorization through a henselian local G-ring at one stage.** Let `p : X ⟶ Spec A` be a
morphism to the spectrum of a henselian local ring, and let `X ⟶ Xᵢ`, `Spec A ⟶ Sᵢ` be a
commutative square over a proper `fᵢ : Xᵢ ⟶ Sᵢ` with `Sᵢ` of finite type over `ℤ`. Let `Aᵢʰ` be the
henselization of the local ring of `Sᵢ` at the image of the closed point. It is a henselian local
Noetherian G-ring and it maps to `A`. If Tag 0A48 holds over henselian local G-rings, then the
fibre of `p` over the closed point maps to the closed fibre of `Xᵢ ×_{Sᵢ} Spec Aᵢʰ`, compatibly
with `X ⟶ Xᵢ ×_{Sᵢ} Spec Aᵢʰ`, and that closed fibre maps to the fibre of `fᵢ`, compatibly with the
maps from the fibre of `p`. -/
theorem exists_factorization_fiber_closedPoint_of_isGRing
    (hG : ∀ (R : Type u) [CommRing R] [HenselianLocalRing R], IsGRing R →
      ∀ {Y : Scheme.{u}} (q : Y ⟶ Spec (.of R)), IsProper q →
        (finiteEtaleBaseChange (pullback.fst q (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (maximalIdeal R)))))).IsEquivalence)
    (A : Type u) [CommRing A] [HenselianLocalRing A] {X Xᵢ Sᵢ : Scheme.{u}}
    (p : X ⟶ Spec (.of A)) (fᵢ : Xᵢ ⟶ Sᵢ) [IsProper fᵢ] [LocallyOfFiniteType (terminal.from Sᵢ)]
    (a : X ⟶ Xᵢ) (π : Spec (.of A) ⟶ Sᵢ) (w : a ≫ fᵢ = p ≫ π) (s : Spec (.of A))
    (hs : s = closedPoint (CommRingCat.of A)) :
    ∃ (Y Y₀ : Scheme.{u}) (b : X ⟶ Y) (r : Y₀ ⟶ Y)
      (z : pullback p ((Spec (.of A)).fromSpecResidueField s) ⟶ Y₀)
      (v : Y₀ ⟶ pullback fᵢ (Sᵢ.fromSpecResidueField (π s))),
      (finiteEtaleBaseChange r).EssSurj ∧ z ≫ r = pullback.fst _ _ ≫ b ∧
        z ≫ v = pullback.lift (pullback.fst _ _ ≫ a)
          (pullback.snd _ _ ≫ Spec.map (π.residueFieldMap s))
          (by
            rw [Category.assoc, w, ← Category.assoc, pullback.condition, Category.assoc,
              Category.assoc, Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]) := by
  classical
  -- the local ring of `Sᵢ` at the image of the closed point is a Noetherian local G-ring
  let Aᵢ := Sᵢ.presheaf.stalk (π s)
  have hGᵢ : IsGRing Aᵢ := isGRing_stalk_of_locallyOfFiniteType_terminal (π s)
  have : IsNoetherianRing Aᵢ := hGᵢ.1
  -- its henselization `B` is a henselian local Noetherian G-ring
  obtain ⟨B, _, _, _, hB⟩ := exists_isHenselization_residueField Aᵢ
  obtain ⟨Bsh, _, _, _, hBsh⟩ := exists_isHenselization_separableClosure Aᵢ
  have : HenselianLocalRing B := hB.henselian
  have : IsLocalHom (algebraMap Aᵢ B) := IsHenselization.isLocalHom (L := ResidueField Aᵢ)
  have hGB : IsGRing B := (isGRing_henselization_and_strictHenselization Aᵢ B Bsh
    (SeparableClosure (ResidueField Aᵢ)) hGᵢ).1
  -- `B` maps to `A` over `Aᵢ`, by the universal property of the henselization
  obtain ⟨ψ₀, hψ₀, hψ₀π⟩ : ∃ ψ₀ : Aᵢ ⟶ CommRingCat.of A,
      IsLocalHom ψ₀.hom ∧ Spec.map ψ₀ ≫ Sᵢ.fromSpecStalk (π s) = π := by
    subst hs
    exact ⟨Scheme.stalkClosedPointTo π, inferInstance,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk π⟩
  let : Algebra Aᵢ A := ψ₀.hom.toAlgebra
  have : IsLocalHom (algebraMap Aᵢ A) := hψ₀
  let ψ : B →ₐ[Aᵢ] A := HenselianLocalRing.indEtaleAlgHom (Sh := A) hB.ind_etale
    (IsHenselization.residueField_map_bijective (R := Aᵢ) (Rh := B)).2
  have hψ : IsLocalHom ψ.toRingHom := ⟨(HenselianLocalRing.isLocalHom_indEtaleAlgHom (Sh := A)
    hB.ind_etale (IsHenselization.residueField_map_bijective (R := Aᵢ) (Rh := B)).2).map_nonunit⟩
  have hψη : CommRingCat.ofHom (algebraMap Aᵢ B) ≫ CommRingCat.ofHom ψ.toRingHom = ψ₀ := by
    ext x
    exact ψ.commutes x
  -- the scheme `Y = Xᵢ ×_{Sᵢ} Spec B`, proper over `Spec B`
  let toS : Spec (.of B) ⟶ Sᵢ :=
    Spec.map (CommRingCat.ofHom (algebraMap Aᵢ B)) ≫ Sᵢ.fromSpecStalk (π s)
  let Y := pullback fᵢ toS
  let q : Y ⟶ Spec (.of B) := pullback.snd fᵢ toS
  have : IsProper q := inferInstance
  let σ : Spec (.of A) ⟶ Spec (.of B) := Spec.map (CommRingCat.ofHom ψ.toRingHom)
  have hσ : σ ≫ toS = π := by
    simp only [σ, toS, ← Category.assoc, ← Spec.map_comp, hψη]
    exact hψ₀π
  let b : X ⟶ Y := pullback.lift a (p ≫ σ) (by rw [w, Category.assoc, hσ])
  -- the closed fibre of `Y`, where Tag 0A48 over `B` applies
  let mkB := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal B)))
  let Y₀ := pullback q mkB
  let r : Y₀ ⟶ Y := pullback.fst q mkB
  have hEq := hG B hGB q inferInstance
  -- the closed point of `Spec A` maps to the closed fibre of `Y`
  obtain ⟨θ, -, hθ⟩ := exists_isIso_comp_specMap_mk_eq_fromSpecResidueField A s hs
  have hle : maximalIdeal B ≤ (maximalIdeal A).comap ψ.toRingHom :=
    (IsLocalRing.maximalIdeal_comap ψ.toRingHom).ge
  let τ := θ ≫ Spec.map (CommRingCat.ofHom (Ideal.quotientMap (maximalIdeal A) ψ.toRingHom hle))
  have hτ : τ ≫ mkB = (Spec (.of A)).fromSpecResidueField s ≫ σ := by
    have hring : CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal B)) ≫
        CommRingCat.ofHom (Ideal.quotientMap (maximalIdeal A) ψ.toRingHom hle) =
        CommRingCat.ofHom ψ.toRingHom ≫
          CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal A)) := by
      ext x
      rfl
    simp only [τ, mkB, σ, Category.assoc, ← Spec.map_comp, hring]
    simp only [Spec.map_comp, ← Category.assoc, hθ]
  let ι := pullback.fst p ((Spec (.of A)).fromSpecResidueField s)
  let z : pullback p ((Spec (.of A)).fromSpecResidueField s) ⟶ Y₀ :=
    pullback.lift (ι ≫ b) (pullback.snd _ _ ≫ τ) (by
      simp only [ι, b, q, Category.assoc, pullback.lift_snd, hτ]
      rw [← Category.assoc, pullback.condition, Category.assoc])
  -- the closed fibre of `Y` maps to the fibre of `fᵢ`
  have hleB : maximalIdeal Aᵢ ≤ (maximalIdeal B).comap (algebraMap Aᵢ B) :=
    (IsLocalRing.maximalIdeal_comap (algebraMap Aᵢ B)).ge
  let κ : Sᵢ.residueField (π s) ⟶ CommRingCat.of (B ⧸ maximalIdeal B) :=
    CommRingCat.ofHom (Ideal.quotientMap (maximalIdeal B) (algebraMap Aᵢ B) hleB)
  have hκ : Spec.map κ ≫ Sᵢ.fromSpecResidueField (π s) = mkB ≫ toS := by
    have hring : Sᵢ.residue (π s) ≫ κ = CommRingCat.ofHom (algebraMap Aᵢ B) ≫
        CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal B)) := by
      ext x
      rfl
    simp only [Scheme.fromSpecResidueField, mkB, toS, ← Category.assoc, ← Spec.map_comp, hring]
  let v : Y₀ ⟶ pullback fᵢ (Sᵢ.fromSpecResidueField (π s)) :=
    pullback.lift (r ≫ pullback.fst _ _) (pullback.snd _ _ ≫ Spec.map κ) (by
      simp only [r, Category.assoc, pullback.condition, hκ]
      rw [← Category.assoc, pullback.condition, Category.assoc])
  refine ⟨Y, Y₀, b, r, z, v, inferInstance, pullback.lift_fst _ _ _, ?_⟩
  apply pullback.hom_ext
  · simp only [z, v, r, ι, b, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
  · simp only [z, v, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
    congr 1
    refine (cancel_mono (Sᵢ.fromSpecResidueField (π s))).mp ?_
    simp only [τ, Category.assoc, hκ, Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
    simp only [← Category.assoc, show θ ≫ Spec.map (CommRingCat.ofHom
      (Ideal.quotientMap (maximalIdeal A) ψ.toRingHom hle)) = τ from rfl, hτ]
    simp only [Category.assoc, hσ]

/-- **Essential surjectivity onto the fibre over the closed point, from the G-ring case.** Let `A`
be a henselian local ring and `p : X ⟶ Spec A` proper. Granted Tag 0A48 over henselian local
G-rings, every finite étale cover of the fibre of `p` over the closed point comes from a finite
étale cover of `X`.

This is the general case of the source's proof. Tag 0A0P writes `p` as the limit of proper
morphisms `Xᵢ ⟶ Sᵢ` with `Sᵢ` of finite type over `ℤ`; the fibre of `p` is the limit of the fibres
of the `Xᵢ ⟶ Sᵢ` over the images `sᵢ` of the closed point, so a finite étale cover of it comes
from a finite étale cover of one of those fibres (Tags 01ZM, 01ZO, 07RP). The latter is pulled
back to the closed fibre of `Xᵢ ×_{Sᵢ} Spec 𝒪_{Sᵢ,sᵢ}ʰ`, which is proper over the henselian local
G-ring `𝒪_{Sᵢ,sᵢ}ʰ` (Tags 07PX, 07QR), where the hypothesis lifts it; and `X` maps to
`Xᵢ ×_{Sᵢ} Spec 𝒪_{Sᵢ,sᵢ}ʰ` because `𝒪_{Sᵢ,sᵢ}ʰ` maps to `A`. -/
theorem essSurj_finiteEtaleBaseChange_fiber_closedPoint_of_isGRing
    (hG : ∀ (R : Type u) [CommRing R] [HenselianLocalRing R], IsGRing R →
      ∀ {Y : Scheme.{u}} (q : Y ⟶ Spec (.of R)), IsProper q →
        (finiteEtaleBaseChange (pullback.fst q (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (maximalIdeal R)))))).IsEquivalence)
    (A : Type u) [CommRing A] [HenselianLocalRing A] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of A)) [IsProper p] (s : Spec (.of A))
    (hs : s = closedPoint (CommRingCat.of A)) :
    (finiteEtaleBaseChange (pullback.fst p ((Spec (.of A)).fromSpecResidueField s))).EssSurj := by
  obtain ⟨I, hI, hne, hdir, D, c, hproper, hftype, haff, ⟨hc⟩, ⟨iso⟩⟩ :=
    exists_isLimit_isProper_finiteType_arrow p
  let := hI
  let := hne
  let := hdir
  have : IsCofilteredOrEmpty Iᵒᵖ := isCofilteredOrEmpty_opposite_of_isDirected
  have : Nonempty Iᵒᵖ := Nonempty.map op hne
  have : IsCofiltered Iᵒᵖ := ⟨⟩
  have : ∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom ((D ⋙ Arrow.leftFunc).map g) :=
    fun g => (haff g).1
  have : ∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom ((D ⋙ Arrow.rightFunc).map g) :=
    fun g => (haff g).2
  -- the same limit, with the arrow `p` itself as its apex
  let c' : Cone D :=
    { pt := Arrow.mk p
      π :=
        { app := fun j => iso.inv ≫ c.π.app j
          naturality := fun i j g =>
            (Category.id_comp _).trans
              ((Category.assoc _ _ _).trans
                (congrArg (fun z => iso.inv ≫ z) (c.w g))).symm } }
  have hc' : IsLimit c' := hc.ofIsoLimit (Cone.ext iso fun j => by simp [c'])
  let φ : (D ⋙ Arrow.leftFunc) ⟶ (D ⋙ Arrow.rightFunc) :=
    { app := fun j => (D.obj j).hom
      naturality := fun _ _ g => (D.map g).w }
  have hp : ∀ j, (Arrow.leftFunc.mapCone c').π.app j ≫ φ.app j =
      p ≫ (Arrow.rightFunc.mapCone c').π.app j := fun j => (c'.π.app j).w
  have hA := Stacks.AlgebraicGeometry.Fibres.isLimitLeftFuncMapCone D c' hc'
  have hB := Stacks.AlgebraicGeometry.Fibres.isLimitRightFuncMapCone D c' hc'
  have hR := Stacks.AlgebraicGeometry.Fibres.residueSpecConeIsLimit (D ⋙ Arrow.rightFunc)
    (Arrow.rightFunc.mapCone c') s hB
  -- the fibre of `p` is the limit of the fibres of the stages
  have hFib := Stacks.AlgebraicGeometry.Fibres.fiberConeIsLimit φ (Arrow.rightFunc.mapCone c') s
    (Arrow.leftFunc.mapCone c') p hp hA hB hR
  have hpr : ∀ j, IsProper (D.obj j).hom := hproper
  have : ∀ j, QuasiCompact (φ.app j) := fun j => (inferInstance : QuasiCompact (D.obj j).hom)
  have : ∀ j, QuasiSeparated (φ.app j) := fun j =>
    (inferInstance : QuasiSeparated (D.obj j).hom)
  have : ∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom
      ((Stacks.AlgebraicGeometry.Fibres.fiberDiagram φ (Arrow.rightFunc.mapCone c') s).map g) :=
    fun g => Stacks.AlgebraicGeometry.Fibres.isAffineHom_fiberDiagram_map φ
      (Arrow.rightFunc.mapCone c') s g
  have := Stacks.AlgebraicGeometry.Fibres.compactSpace_fiberDiagram_obj φ
    (Arrow.rightFunc.mapCone c') s
  have := Stacks.AlgebraicGeometry.Fibres.quasiSeparatedSpace_fiberDiagram_obj φ
    (Arrow.rightFunc.mapCone c') s
  refine essSurj_finiteEtaleBaseChange_of_isLimit_of_factors _ _ hFib _ fun j => ?_
  have : LocallyOfFiniteType (terminal.from (D.obj j).right) := (hftype j).1
  exact exists_factorization_fiber_closedPoint_of_isGRing hG
    A p (D.obj j).hom (c'.π.app j).left (c'.π.app j).right (c'.π.app j).w s hs

/-- **Tag 0A48 for a henselian local ring, from the G-ring case.** Let `A` be a henselian local
ring and `p : X ⟶ Spec A` proper. Granted Tag 0A48 over henselian local Noetherian G-rings, base
change to the closed fibre `X ×_{Spec A} Spec (A/𝔪)` is an equivalence on finite étale covers.

Full faithfulness is reduced to essential surjectivity for the schemes finite étale over `X` by
`isEquivalence_finiteEtaleBaseChange_of_isProper_of_henselianPair_of_essSurj`, and essential
surjectivity is `essSurj_finiteEtaleBaseChange_fiber_closedPoint_of_isGRing`. -/
theorem isEquivalence_finiteEtaleBaseChange_closedFibre_of_isGRing
    (hG : ∀ (R : Type u) [CommRing R] [HenselianLocalRing R], IsGRing R →
      ∀ {Y : Scheme.{u}} (q : Y ⟶ Spec (.of R)), IsProper q →
        (finiteEtaleBaseChange (pullback.fst q (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (maximalIdeal R)))))).IsEquivalence)
    (A : Type u) [CommRing A] [HenselianLocalRing A] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of A)) [IsProper p] :
    (finiteEtaleBaseChange (pullback.fst p
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal A)))))).IsEquivalence :=
  isEquivalence_finiteEtaleBaseChange_of_isProper_of_henselianPair_of_essSurj A (maximalIdeal A)
    (henselianPair_maximalIdeal A) p fun P =>
      have := isProper_comp_of_finiteEtaleOver p P
      essSurj_finiteEtaleBaseChange_closedFibre_of_fiber A (P.hom ≫ p)
        (essSurj_finiteEtaleBaseChange_fiber_closedPoint_of_isGRing hG A (P.hom ≫ p) _ rfl)

/-- **Stage 3 of the proof of Tag 0A48: the general henselian local ring.** The conclusion of
Tag 0A48 for every henselian local ring, `ProperHenselianFiniteEtaleEquivalence`, follows from its
restriction to henselian local Noetherian G-rings. -/
theorem properHenselianFiniteEtaleEquivalence_of_isGRing
    (hG : ∀ (R : Type u) [CommRing R] [HenselianLocalRing R], IsGRing R →
      ∀ {Y : Scheme.{u}} (q : Y ⟶ Spec (.of R)), IsProper q →
        (finiteEtaleBaseChange (pullback.fst q (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (maximalIdeal R)))))).IsEquivalence) :
    ProperHenselianFiniteEtaleEquivalence.{u} :=
  fun R _ _ _ p hp =>
    have := hp
    isEquivalence_finiteEtaleBaseChange_closedFibre_of_isGRing hG R p

/-! ### The three stages of Tag 0A48 together -/

/-- **Tag 0A48 for proper schemes over henselian local rings, granted Grothendieck existence for
finite sheaves of algebras.** If `AdicFiniteAlgebraAlgebraization` holds for every proper scheme
over every complete local Noetherian ring, then `ProperHenselianFiniteEtaleEquivalence` holds:
for every henselian local ring `R` and every proper `p : Y ⟶ Spec R`, base change to the closed
fibre is an equivalence on finite étale covers.

This composes the three stages of the source's proof: the complete case
(`properCompleteLocalFiniteEtaleEquivalence_of_adicFiniteAlgebraAlgebraization`), the henselian
local Noetherian G-ring case (`isEquivalence_finiteEtaleBaseChange_of_isProper_of_isGRing`) and
the general case (`properHenselianFiniteEtaleEquivalence_of_isGRing`). -/
theorem properHenselianFiniteEtaleEquivalence_of_adicFiniteAlgebraAlgebraization
    (halg : ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
      [IsAdicComplete (IsLocalRing.maximalIdeal R) R] {Y : Scheme.{u}} (p : Y ⟶ Spec (.of R)),
      IsProper p → AdicFiniteAlgebraAlgebraization R (IsLocalRing.maximalIdeal R) p) :
    ProperHenselianFiniteEtaleEquivalence.{u} := by
  refine properHenselianFiniteEtaleEquivalence_of_isGRing ?_
  intro R _ _ hG Y q hq
  exact isEquivalence_finiteEtaleBaseChange_of_isProper_of_isGRing
    (properCompleteLocalFiniteEtaleEquivalence_of_adicFiniteAlgebraAlgebraization halg) R hG q

/-- **Stacks Project, Tag 0A48.** Let `A` be a henselian local ring and `X` a proper scheme over
`A` with closed fibre `X₀ = X ×_{Spec A} Spec (A ⧸ 𝔪)`. Then base change
`FÉt_X ⥤ FÉt_{X₀}, U ↦ U ×_X X₀` is an equivalence of categories.

The three stages of the source's proof are composed by
`properHenselianFiniteEtaleEquivalence_of_adicFiniteAlgebraAlgebraization`; its one input,
Grothendieck existence for finite sheaves of algebras over a proper scheme over a complete local
Noetherian ring, is `adicFiniteAlgebraAlgebraization_of_isProper` (from Stacks 088C). -/
@[stacks 0A48,
  sga "1 X 2.1" "more general",
  sga "3 X 4.0" "more general",
  sga "3 XXIV 8.1.2" "more general",
  sga "4 XII 5.9",
  sga "4½ Arcata 4.2.1" "more general",
  sga "7 IX 2.2.4" "more general",
  sga "7 XIII 1.2.1" "more general"]
theorem isEquivalence_finiteEtaleBaseChange_of_isProper_of_henselianLocalRing
    (A : Type u) [CommRing A] [HenselianLocalRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsProper f] :
    (finiteEtaleBaseChange (pullback.fst f
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal A)))))).IsEquivalence :=
  properHenselianFiniteEtaleEquivalence_of_adicFiniteAlgebraAlgebraization
    (fun R _ _ _ _ _ p hp => have := hp
      adicFiniteAlgebraAlgebraization_of_isProper R (IsLocalRing.maximalIdeal R) p)
    A f inferInstance

/-- Tag 0A48 (`isEquivalence_finiteEtaleBaseChange_of_isProper_of_henselianLocalRing`) in the
shape `ProperHenselianFiniteEtaleEquivalence` consumed by the fundamental-group results. -/
@[ega "IV 18.5.15" "local Henselian case",
  sga "3 X 4.0" "more general",
  sga "7 IX 2.2.4" "more general"]
theorem properHenselianFiniteEtaleEquivalence : ProperHenselianFiniteEtaleEquivalence.{u} :=
  fun R _ _ _ p hp => have := hp
    isEquivalence_finiteEtaleBaseChange_of_isProper_of_henselianLocalRing R p

end AlgebraicGeometry
