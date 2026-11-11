module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionDiagonal
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionRepresents
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitSpaceSeparated
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSolutionClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase

/-!
# Separatedness of a solution of Artin's contraction problem

In the situation of Stacks 0GH8, let `(f : X' ⟶ X, T, a)` be a solution whose open subspace `U`
is the complement of `T`, with `X` locally of finite type over `S`. If `X' → S` and `W → S` are
separated, then `X → S` is separated.

Indeed, by Stacks 0GHB the solution identifies Artin's functor `F` with `Mor_S(-, X)` on locally
Noetherian schemes over `S`, and by Stacks 0GHF the diagonal of `F` is representable by closed
immersions. For a surjective étale atlas `N → X` with kernel pair `R = N ×_X N`, the scheme `R`
represents the fibre product of the diagonal with `h_{N ×_S N} → F × F`, so `R → N ×_S N` is a
closed immersion, and `X` is separated over `S` by Stacks 02WZ.

## Main results

* `AlgebraicGeometry.Artin.ContractionSituation.Solution.isSeparated_terminal_from`

## References

* [Stacks Project, Tag 0GHB](https://stacks.math.columbia.edu/tag/0GHB)
* [Stacks Project, Tag 0GHF](https://stacks.math.columbia.edu/tag/0GHF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Artin.ContractionSituation.Solution

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {c : ContractionSituation B S hS} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **A solution of Artin's contraction problem is separated.** In the situation of Stacks 0GH8,
if `X' → S` and `W → S` are separated, a solution `(f : X' ⟶ X, T, a)` whose open subspace `U` is
the complement of `T` and whose space `X` is locally of finite type over `S` is separated over
`S`: the diagonal of Artin's functor is representable by closed immersions (Stacks 0GHF) and that
functor is `Mor_S(-, X)` on locally Noetherian schemes (Stacks 0GHB). -/
theorem isSeparated_terminal_from (s : c.Solution X)
    (hU : Set.range (Space.pointsMap B S hS s.U.toFunctor s.U.ι) = s.Tᶜ)
    (hX' : Space.IsSeparated B S hS (terminal.from c.X'))
    (hW : FormalSpace.IsSeparatedMorphism B S hS (terminal.from c.W))
    (hft : Space.IsLocallyOfFiniteType B S hS (terminal.from X)) :
    Space.IsSeparated B S hS (terminal.from X) := by
  have : IsLocallyNoetherian S := c.isLocallyNoetherian_base
  let T := BigFppfOver.toScheme B S hS
  have : PreservesLimitsOfShape WalkingCospan T := comp_preservesLimitsOfShape _ _
  obtain ⟨N, q, hqs, hqe⟩ := s.isAlgebraicSpace_X.exists_atlas
  let R := hqe.rep.pullback q
  let sR : R ⟶ N := yoneda.preimage (hqe.rep.fst q)
  let tR : R ⟶ N := hqe.rep.snd q
  have hR : IsPullback (yoneda.map sR) (yoneda.map tR) q q := by
    rw [Functor.map_preimage]
    exact hqe.rep.isPullback q
  let V := ⊤_ (BigFppfOver B S hS)
  let n₀ : N ⟶ V := terminal.from N
  let pY : X ⟶ yoneda.obj V := terminal.from X ≫ (Space.yonedaTerminalIso B S hS).inv
  have hn₀ : yoneda.map n₀ = q ≫ pY := (Space.isTerminal_yoneda_obj_terminal B S hS).hom_ext _ _
  let ι : R ⟶ pullback n₀ n₀ := pullback.lift sR tR (Space.kernelPair_comp_eq hR hn₀)
  -- the schemes `N`, `R` and `N ×_S N` are locally Noetherian
  have hNN : IsLocallyNoetherian (T.obj N) :=
    Space.isLocallyNoetherian_of_presheafEtale B S hS hft N q hqe
  have hRN : IsLocallyNoetherian (T.obj R) := by
    have : Etale (T.map tR) := hqe.property_snd q
    exact LocallyOfFiniteType.isLocallyNoetherian (T.map tR)
  have hPN : IsLocallyNoetherian (T.obj (pullback n₀ n₀)) := by
    have h1 : LocallyOfFiniteType (T.map n₀) := by
      have := Space.locallyOfFiniteType_hom_of_presheafEtale B S hS hft N q hqe
      have e : T.map n₀ = B.inclusion.map N.hom ≫ (Space.toSchemeTerminalIso B S hS).inv := by
        rw [← Space.toScheme_map_terminal_from B S hS N, Category.assoc, Iso.hom_inv_id,
          Category.comp_id]
      rw [e]
      infer_instance
    have : LocallyOfFiniteType (T.map (pullback.fst n₀ n₀)) :=
      MorphismProperty.of_isPullback ((IsPullback.of_hasPullback n₀ n₀).map T).flip h1
    exact LocallyOfFiniteType.isLocallyNoetherian (T.map (pullback.fst n₀ n₀))
  let Rn : LocallyNoetherianOver B S hS := ⟨R, hRN⟩
  let Pn : LocallyNoetherianOver B S hS := ⟨pullback n₀ n₀, hPN⟩
  let ιn : Rn ⟶ Pn := ObjectProperty.homMk ι
  have hι₁ : ι ≫ pullback.fst n₀ n₀ = sR := pullback.lift_fst _ _ _
  have hι₂ : ι ≫ pullback.snd n₀ n₀ = tR := pullback.lift_snd _ _ _
  have : Mono ιn := by
    refine ⟨fun {Z} g h e => ?_⟩
    have e' : g.hom ≫ ι = h.hom ≫ ι := congrArg (fun k => k.hom) e
    ext : 1
    apply yoneda.map_injective
    apply hR.hom_ext
    · rw [← Functor.map_comp, ← Functor.map_comp, ← hι₁, ← Category.assoc, e', Category.assoc]
    · rw [← Functor.map_comp, ← Functor.map_comp, ← hι₂, ← Category.assoc, e', Category.assoc]
  -- the two elements of `F(N ×_S N)` given by the two projections
  let α := s.contractionFunctorIso hU
  let xq : X.obj (op N) := yonedaEquiv q
  let t₁ : (contractionFunctor c).obj (op Pn) :=
    α.inv.app (op Pn) (ULift.up (X.map (pullback.fst n₀ n₀).op xq))
  let t₂ : (contractionFunctor c).obj (op Pn) :=
    α.inv.app (op Pn) (ULift.up (X.map (pullback.snd n₀ n₀).op xq))
  have hnat : ∀ {A : LocallyNoetherianOver B S hS} (φ : A ⟶ Pn) (x : X.obj (op Pn.obj)),
      (contractionFunctor c).map φ.op (α.inv.app (op Pn) (ULift.up x)) =
        α.inv.app (op A) (ULift.up (X.map φ.hom.op x)) := fun φ x =>
    (inv_app_map_morOnLocallyNoetherian c α φ (ULift.up x)).symm
  have hinj : ∀ (A : LocallyNoetherianOver B S hS) {x y : X.obj (op A.obj)},
      α.inv.app (op A) (ULift.up x) = α.inv.app (op A) (ULift.up y) → x = y := fun A x y h => by
    exact congrArg ULift.down ((mono_iff_injective (α.inv.app (op A))).1 inferInstance h)
  have key := isPullback_diag_of_factors_iff.{u + 1} (contractionFunctor c) ιn t₁ t₂
    (fun A φ => by
      simp only [t₁, t₂, hnat]
      constructor
      · rintro ⟨ψ, hψ⟩
        have hφ : φ.hom = ψ.hom ≫ ι := (congrArg (fun k => k.hom) hψ).symm
        rw [hφ]
        congr 2
        simp only [xq, ← op_comp, ← Functor.map_comp_apply, Category.assoc, hι₁, hι₂]
        rw [yonedaEquiv_naturality, yonedaEquiv_naturality, Functor.map_comp, Functor.map_comp,
          Category.assoc, Category.assoc, hR.w]
      · intro h
        have h' := hinj A h
        simp only [xq, yonedaEquiv_naturality] at h'
        have hw := yonedaEquiv.injective h'
        have hw' : (yoneda.map φ.hom ≫ yoneda.map (pullback.fst n₀ n₀)) ≫ q =
            (yoneda.map φ.hom ≫ yoneda.map (pullback.snd n₀ n₀)) ≫ q := by
          simpa only [Category.assoc] using hw
        let ψ : A.obj ⟶ R := yoneda.preimage (hR.lift _ _ hw')
        have hψ₁ : yoneda.map ψ ≫ yoneda.map sR =
            yoneda.map φ.hom ≫ yoneda.map (pullback.fst n₀ n₀) := by
          rw [Functor.map_preimage]
          exact hR.lift_fst _ _ hw'
        have hψ₂ : yoneda.map ψ ≫ yoneda.map tR =
            yoneda.map φ.hom ≫ yoneda.map (pullback.snd n₀ n₀) := by
          rw [Functor.map_preimage]
          exact hR.lift_snd _ _ hw'
        refine ⟨ObjectProperty.homMk ψ, ?_⟩
        ext : 1
        apply pullback.hom_ext
        · apply yoneda.map_injective
          change yoneda.map ((ψ ≫ ι) ≫ pullback.fst n₀ n₀) = _
          rw [Category.assoc, hι₁, Functor.map_comp, hψ₁, Functor.map_comp]
        · apply yoneda.map_injective
          change yoneda.map ((ψ ≫ ι) ≫ pullback.snd n₀ n₀) = _
          rw [Category.assoc, hι₂, Functor.map_comp, hψ₂, Functor.map_comp])
  have hci : _root_.AlgebraicGeometry.IsClosedImmersion (T.map ι) :=
    (relative_isClosedImmersion_diag_contractionFunctor c hX' hW).property _ _ _ key
  have hsep : Space.IsSeparated B S hS pY :=
    Space.isSeparated_of_isClosedImmersion_lift_kernelPair s.isAlgebraicSpace_X pY hqs hqe hR hn₀
      hci
  exact Space.isSeparated_of_arrowIso B S hS pY (terminal.from X) (𝟙 X)
    (Space.yonedaTerminalIso B S hS).hom (terminal.hom_ext _ _) hsep

end AlgebraicGeometry.Artin.ContractionSituation.Solution

end
