module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFreeOfRank
public import StacksFrontier.AlgebraicGeometry.Different.FiniteSyntomicMorphisms.AlgebraAxioms

open AlgebraicGeometry.FiniteFreeAlgebra

/-!
# Rank of the universal finite free family

The universal affine family of commutative algebras of rank `d` is finite locally free of rank
`d` over its parameter scheme. So the universal family is a finite syntomic morphism of the
expected degree.

## Main results

* `AlgebraicGeometry.universalFamily_isFiniteLocallyFreeOfRank` states that the universal family
  has rank `d`.
* `AlgebraicGeometry.universalFamily_isFinite_flat_locallyOfFinitePresentation` reads off that
  the universal family is finite, flat and locally of finite presentation.

## Implementation notes

Finite freeness of a morphism of schemes with a fixed rank is `Stacks.Morphisms`'
`IsFiniteLocallyFreeOfRank`, which asks that the morphism be affine and that the pushforward of
the structure sheaf be finite locally free of that rank. The algebra structure used to form the
universal total space and family is the canonical one supplied by the algebra-axioms part of
Tag 0FKZ.

The rank is computed by identifying the pushforward of the structure sheaf with the tilde of the
global sections, then with the tilde of a finitely supported function module of index type
`Fin d`, which is free of rank `d`. The identification of global sections uses the explicit
coordinates of the universal carrier, which is why the algebra structure is carried as data
rather than as instances.

## References

* [Stacks Project, Tag 0FKZ](https://stacks.math.columbia.edu/tag/0FKZ)
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory Opposite

namespace AlgebraicGeometry

-- Transporting local generator data requires unfolding the sheaf section maps.
private lemma rank_of_module_iso {S : Scheme.{u}} {M N : S.Modules} (e : M ≅ N)
    (r : ℕ) (h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N r := by
  obtain ⟨q, hfree, hrank⟩ := h.exists_isFiniteLocallyFreeOfRankData
  let q' : N.LocalGeneratorsData := {
    I := q.I
    X := q.X
    coversTop := q.coversTop
    generators i := (q.generators i).ofEpi
      ((SheafOfModules.overFunctor _ (q.X i)).mapIso e).hom }
  constructor
  refine ⟨q', ⟨fun i => ?_⟩, hrank⟩
  simp only [q', SheafOfModules.GeneratingSections.ofEpi_π]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ (hfree.isIso i) inferInstance

private lemma free_sheaf_rank (A : CommRingCat.{u}) (d : ℕ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (SheafOfModules.free (R := (Spec A).ringCatSheaf) (ULift.{u} (Fin d))) d := by
  let q := (SheafOfModules.free.generatingSections
    (R := (Spec A).ringCatSheaf) (ULift.{u} (Fin d))).localGeneratorsData
  exact AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.mk.{u, u, u}
    (M := SheafOfModules.free (R := (Spec A).ringCatSheaf) (ULift.{u} (Fin d)))
    (r := d) ⟨q, inferInstance, fun _ => ⟨Equiv.ulift⟩⟩

private lemma tilde_finsupp_rank (A : CommRingCat.{u}) (d : ℕ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (AlgebraicGeometry.tilde (ModuleCat.of A (ULift.{u} (Fin d) →₀ A))) d :=
  rank_of_module_iso
    (AlgebraicGeometry.tildeFinsupp (R := A) (ULift.{u} (Fin d))).symm d (free_sheaf_rank A d)

-- The base scheme uses the lifted coefficient ring, acting through `ULift.down`.
private noncomputable def universalCarrierLinearEquiv (d : ℕ) [NeZero d]
    (s : UniversalAlgebraStructure d) :
    letI : CommRing (UniversalFiniteFreeModule d) := s.ring
    letI : Algebra
      (universalRing d)
      (UniversalFiniteFreeModule d) := s.algebra
    letI : Module (ULift.{u}
      (universalRing d))
      (UniversalFiniteFreeModule d) :=
        Module.compHom
          (UniversalFiniteFreeModule d)
          ((algebraMap
            (universalRing d)
            (UniversalFiniteFreeModule d)).comp
              ULift.ringEquiv.toRingHom)
    UniversalFiniteFreeModule d ≃ₗ[
      ULift.{u}
        (universalRing d)]
        (ULift.{u} (Fin d) →₀ ULift.{u}
          (universalRing d)) := by
  letI := s.ring
  letI := s.algebra
  letI : Module (ULift.{u} (universalRing d)) (UniversalFiniteFreeModule d) :=
    Module.compHom (UniversalFiniteFreeModule d)
      ((algebraMap (universalRing d) (UniversalFiniteFreeModule d)).comp
        ULift.ringEquiv.toRingHom)
  let e : UniversalFiniteFreeModule d ≃ₗ[ULift.{u} (universalRing d)]
      (Fin d → ULift.{u} (universalRing d)) := {
    toFun := fun x i => ULift.up (x.coeff i)
    invFun := fun f => ⟨fun i => (f i).down⟩
    left_inv := by intro x; cases x; rfl
    right_inv := by intro f; rfl
    map_add' := by
      intro x y
      funext i
      exact ULift.ext _ _ (s.add_coeff x y i)
    map_smul' := by
      intro a x
      funext i
      apply ULift.ext
      change ((algebraMap _ _ a.down * x).coeff i) = a.down * x.coeff i
      rw [s.mul_eq]
      simp only [universalMultiplication]
      simp only [s.algebraMap_coeff]
      simp [universalStructureConstant_zero_left] }
  let ep := LinearEquiv.piCongrLeft (ULift.{u} (universalRing d))
    (fun _ : ULift.{u} (Fin d) => ULift.{u} (universalRing d)) Equiv.ulift.symm
  exact e.trans (ep.trans (Finsupp.linearEquivFunOnFinite (ULift.{u} (universalRing d))
    (ULift.{u} (universalRing d)) (ULift.{u} (Fin d))).symm)

private noncomputable def pushforwardGammaEquiv (A B : CommRingCat.{u}) (φ : A ⟶ B) :
    let f := Spec.map φ
    let M : (Spec B).Modules := SheafOfModules.unit (Spec B).ringCatSheaf
    let Q : (Spec A).Modules := (Scheme.Modules.pushforward f).obj M
    letI : Module ↑A ↑(Γ(Q, ⊤)) := Module.compHom (Γ(Q, ⊤)) (Scheme.ΓSpecIso A).inv.hom
    letI : Module ↑A ↑B := Module.compHom B φ.hom
    Γ(Q, ⊤) ≃ₗ[A] B := by
  let f := Spec.map φ
  let M : (Spec B).Modules := SheafOfModules.unit (Spec B).ringCatSheaf
  let Q : (Spec A).Modules := (Scheme.Modules.pushforward f).obj M
  letI : Module ↑A ↑(Γ(Q, ⊤)) := Module.compHom (Γ(Q, ⊤)) (Scheme.ΓSpecIso A).inv.hom
  letI : Module ↑A ↑B := Module.compHom B φ.hom
  let E := (AlgebraicGeometry.pushforwardCompModulesSpecToSheafIso φ).app M
  let eTop := E.hom.hom.app (op ⊤)
  let eInvTop := E.inv.hom.app (op ⊤)
  let e := Iso.mk eTop eInvTop (congrArg (fun g => g.hom.app (op ⊤)) E.hom_inv_id)
    (congrArg (fun g => g.hom.app (op ⊤)) E.inv_hom_id)
  let srcIso := (ModuleCat.restrictScalars φ.hom).mapIso
    (AlgebraicGeometry.tilde.isoTop (ModuleCat.of B B))
  exact e.toLinearEquiv.trans srcIso.toLinearEquiv.symm


/-- The universal affine family of rank-`d` commutative algebras is finite
locally free of rank `d`. -/
@[stacks 0FKZ "finite_free_rank"]
theorem universalFamily_isFiniteLocallyFreeOfRank (d : ℕ) [NeZero d] :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      (universalFamily.{u} d (universalAlgebraStructure d)) d := by
  let s := universalAlgebraStructure d
  let := s.ring
  let := s.algebra
  let φ : CommRingCat.of (ULift.{u} (universalRing d)) ⟶
      CommRingCat.of (ULift.{u} (UniversalFiniteFreeModule d)) :=
    CommRingCat.ofHom (RingHom.ulift (algebraMap (universalRing d) (UniversalFiniteFreeModule d)))
  let f := Spec.map φ
  show Stacks.Morphisms.IsFiniteLocallyFreeOfRank f d
  let Q : (Spec (CommRingCat.of (ULift.{u} (universalRing d)))).Modules :=
    (Scheme.Modules.pushforward f).obj
      (SheafOfModules.unit
        (Spec (CommRingCat.of (ULift.{u} (UniversalFiniteFreeModule d)))).ringCatSheaf)
  have hQ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} Q d := by
    let B := ULift.{u} (UniversalFiniteFreeModule d)
    let R := ULift.{u} (universalRing d)
    let : Module ↑(CommRingCat.of R) ↑(Γ(Q, ⊤)) :=
      Module.compHom (Γ(Q, ⊤)) (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    let _ : Module R (UniversalFiniteFreeModule d) :=
      Module.compHom (UniversalFiniteFreeModule d)
        ((algebraMap (universalRing d) (UniversalFiniteFreeModule d)).comp
          ULift.ringEquiv.toRingHom)
    let eCarrier := (ULift.moduleEquiv : B ≃ₗ[R] UniversalFiniteFreeModule d).trans
      (universalCarrierLinearEquiv d s)
    let eGlobal := (pushforwardGammaEquiv (CommRingCat.of R) (CommRingCat.of B) φ).trans eCarrier
    let eSheaf := (AlgebraicGeometry.tilde.functor (CommRingCat.of R)).mapIso eGlobal.toModuleIso
    have hTilde : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        (AlgebraicGeometry.tilde (ModuleCat.of (↑(CommRingCat.of R)) (Γ(Q, ⊤)))) d :=
      rank_of_module_iso eSheaf.symm d (tilde_finsupp_rank (CommRingCat.of R) d)
    have : IsIso Q.fromTildeΓ := AlgebraicGeometry.isIso_fromTildeΓ_pushforward φ
      (SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf)
    exact rank_of_module_iso (asIso Q.fromTildeΓ) d hTilde
  exact .mk (toIsAffineHom := by infer_instance) (toIsFiniteLocallyFreeOfRank := hQ)

/-- The universal finite free family is finite, flat and locally of finite presentation, being
finite locally free of rank `d` (Tag 02KB). -/
theorem universalFamily_isFinite_flat_locallyOfFinitePresentation (d : ℕ) [NeZero d] :
    IsFinite (universalFamily.{u} d (universalAlgebraStructure d)) ∧
      Flat (universalFamily.{u} d (universalAlgebraStructure d)) ∧
        LocallyOfFinitePresentation (universalFamily.{u} d (universalAlgebraStructure d)) := by
  have : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      (universalFamily.{u} d (universalAlgebraStructure d)) d :=
    universalFamily_isFiniteLocallyFreeOfRank.{u} d
  exact (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation _).mp
    (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ d)


end AlgebraicGeometry
