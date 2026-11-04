module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.GaloisTrivializationExists
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.FiniteEtaleCovers
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TopologicalInvarianceFundamental.Thickening

/-!
# Finite locally constant sheaves of sets on Mathlib's small étale site are represented on
finite étale covers

Let `P` be a finite locally constant sheaf of sets on Mathlib's small étale site `X.Etale`. Then
there is a finite étale cover `Y ⟶ X` and a section `u ∈ P(Y)` such that, for every finite étale
cover `A ⟶ X`, pulling `u` back along `X`-morphisms `A ⟶ Y` is a bijection
`Hom_X(A, Y) ≃ P(A)`.

This is Stacks 03RV, proved in the library for the size-bounded small étale site
`AlgebraicGeometry.SmallEtale B X hX` of Stacks 021B
(`Stacks.EtaleCohomology.isFiniteLocallyConstant_iff_finiteEtaleRepresentable`), transported to
Mathlib's site along the dense subsite inclusion `AlgebraicGeometry.SmallEtale.toEtaleSite`, as
in the proof of `AlgebraicGeometry.exists_finiteEtale_trivialization`. Every finite étale cover
of `X` is an object of the size-bounded site (`AlgebraicGeometry.smallEtaleOfFiniteEtale`), so
the representation on finite étale covers is read off from the representation there.

## Main results

* `AlgebraicGeometry.exists_finiteEtaleOver_bijective_of_isFiniteLocallyConstant` — the
  statement above, with the nonemptiness of `Y` as soon as `P` has a section over a nonempty
  étale scheme.

## References

* [Stacks Project, Tag 03RV](https://stacks.math.columbia.edu/tag/03RV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-- **A finite locally constant sheaf of sets on Mathlib's small étale site is represented, on
finite étale covers, by a finite étale cover.** -/
theorem exists_finiteEtaleOver_bijective_of_isFiniteLocallyConstant {X : Scheme.{u}}
    (P : Sheaf X.smallEtaleTopology (Type (u + 1)))
    [Stacks.ConstantSheaf.IsFiniteLocallyConstant X.smallEtaleTopology P] :
    ∃ (Y : FiniteEtaleOver X) (ν : P.obj.obj (op ((finiteEtaleToEtale X).obj Y))),
      (∀ A : FiniteEtaleOver X,
        Function.Bijective (fun f : A ⟶ Y ↦ P.obj.map ((finiteEtaleToEtale X).map f).op ν)) ∧
      ∀ W : X.Etale, Nonempty W.left → Nonempty (P.obj.obj (op W)) → Nonempty Y.left := by
  let B := BigEtaleSite.containing X
  have hXB : B.Contains X := BigEtaleSite.contains_containing X
  let G := SmallEtale.toEtaleSite B X hXB
  let QB := (G.sheafPushforwardContinuous (Type (u + 1)) (SmallEtale.topology B X hXB)
    X.smallEtaleTopology).obj P
  have : Stacks.ConstantSheaf.IsFiniteLocallyConstant (SmallEtale.topology B X hXB) QB :=
    Stacks.ConstantSheaf.isFiniteLocallyConstant_sheafPushforwardContinuous _ _ G _
  obtain ⟨V, hVfin, ⟨φ⟩⟩ :=
    (Stacks.EtaleCohomology.isFiniteLocallyConstant_iff_finiteEtaleRepresentable B ⟨X, hXB⟩
      QB).1 this
  let ψ := φ ≪≫ ((Sheaf.uliftYonedaIsoSheafifiedYoneda (SmallEtale.topology B X hXB)).app V).symm
  let Y : FiniteEtaleOver X := MorphismProperty.Over.mk ⊤ (G.obj V).hom ⟨hVfin, (G.obj V).prop⟩
  let eY : (finiteEtaleToEtale X).obj Y ≅ G.obj V :=
    MorphismProperty.Over.isoMk (Iso.refl _) (by simp; rfl)
  let ν' : P.obj.obj (op (G.obj V)) := ψ.inv.hom.app (op V) (ULift.up (𝟙 V))
  let ν : P.obj.obj (op ((finiteEtaleToEtale X).obj Y)) := P.obj.map eY.hom.op ν'
  refine ⟨Y, ν, fun A => ?_, fun W ⟨w⟩ ⟨t⟩ => ?_⟩
  swap
  · obtain ⟨W', g, w₀, -⟩ := SmallEtale.exists_obj_mem_range B X hXB W w
    let h : W' ⟶ V := (ψ.hom.hom.app (op W') (P.obj.map g.op t)).down
    exact ⟨(G.map h).left.base w₀⟩
  let AB : SmallEtale B X hXB := smallEtaleOfFiniteEtale (X := ⟨X, hXB⟩) A
  let eA : G.obj AB ≅ (finiteEtaleToEtale X).obj A := MorphismProperty.Over.isoMk (Iso.refl _) (by
    show 𝟙 A.left ≫ A.hom = B.inclusion.map AB.obj.hom
    rw [smallEtaleOfFiniteEtale_hom (X := ⟨X, hXB⟩) A]
    simp)
  let hG : G.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful G
  have key : ∀ f : A ⟶ Y, P.obj.map ((finiteEtaleToEtale X).map f).op ν =
      P.obj.map eA.inv.op (ψ.inv.hom.app (op AB)
        (ULift.up (hG.preimage (eA.hom ≫ (finiteEtaleToEtale X).map f ≫ eY.hom)))) := by
    intro f
    let g := hG.preimage (eA.hom ≫ (finiteEtaleToEtale X).map f ≫ eY.hom)
    have h1 := congrArg (fun φ => φ (ULift.up (𝟙 V) : ULift.{u + 1} (V ⟶ V)))
      (ψ.inv.hom.naturality g.op)
    have h2 : ψ.inv.hom.app (op AB) (ULift.up g) = P.obj.map (G.map g).op ν' := by
      refine Eq.trans ?_ (h1.trans ?_)
      · show _ = (ψ.inv.hom.app (op AB))
          (((GrothendieckTopology.uliftYoneda.{u + 1} (SmallEtale.topology B X hXB)).obj V).obj.map
            g.op (ULift.up (𝟙 V)))
        congr 1
      · rfl
    show _ = P.obj.map eA.inv.op (ψ.inv.hom.app (op AB) (ULift.up g))
    rw [h2, hG.map_preimage]
    simp only [ν, ← Functor.map_comp_apply, ← op_comp, Iso.inv_hom_id_assoc]
  rw [show (fun f : A ⟶ Y ↦ P.obj.map ((finiteEtaleToEtale X).map f).op ν) =
      (P.obj.map eA.inv.op) ∘ (ψ.inv.hom.app (op AB)) ∘ ULift.up ∘ hG.preimage ∘
        (fun k => eA.hom ≫ k ≫ eY.hom) ∘ (finiteEtaleToEtale X).map from funext key]
  exact (P.obj.mapIso eA.op).symm.toEquiv.bijective.comp
    ((((sheafToPresheaf _ _).mapIso ψ).app (op AB)).symm.toEquiv.bijective.comp
      (Equiv.ulift.symm.bijective.comp (hG.homEquiv.symm.bijective.comp
        ((Iso.homCongr eA.symm eY).bijective.comp
          ((finiteEtaleToEtaleFullyFaithful X).map_bijective A Y)))))

end AlgebraicGeometry

end
