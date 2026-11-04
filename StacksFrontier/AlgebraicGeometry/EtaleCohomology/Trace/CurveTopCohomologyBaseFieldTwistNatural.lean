module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveTopCohomologyBaseFieldTwist
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportTwistTransportNatural

/-!
# `H²` of a sheaf pulled back from the base field, naturally in the coefficients

Let `X` be proper over a finite field `k` with structure morphism `g`, such that `X_k̄` is a
smooth proper curve, and let `F₀` be a sheaf of `ℤ/m`-modules on `Spec k` identified over `k̄`
with the constant sheaf `Q` by `u₀`, compatibly with the Frobenius twists and an endomorphism `B`
of `Q`. The isomorphism `H²(X_k̄, g⁻¹ F₀) ≅ Q` with `π_X^* = q · B`
(`Stacks.EtaleCohomology.exists_addEquiv_compactSupportSheafCohomology_two_inverseImage_of_twist`)
can be chosen to carry `(g⁻¹ s₀)_*` to `s` for all endomorphisms `s₀` of `F₀` and `s` of `Q`
which `u₀` intertwines.

## Main results

* `exists_addEquiv_compactSupportSheafCohomology_two_inverseImage_of_twist_natural`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k))
  [LocallyOfFiniteType g] [QuasiCompact g] [IsSeparated g] [IsProper g]
  (kbar : Type u) [Field kbar] [Algebra k kbar] (m : ℕ) [NeZero m] (p q : ℕ) [Fact p.Prime]
  [CharP k p] (hcard : Fintype.card k = p ^ q)
  [IsAlgClosed kbar] [IsCurve k g]
  [IsCurve kbar (pullback.snd (Over.mk g).hom (specAlgebraMap k kbar))]
  [Smooth (pullback.snd (Over.mk g).hom (specAlgebraMap k kbar))]
  [IsProper (pullback.snd (Over.mk g).hom (specAlgebraMap k kbar))]

include hcard in
/-- **`H²(X_k̄, g⁻¹ F₀) ≅ Q` with `π_X^* = q · B`, naturally in the coefficients**: the
isomorphism of `exists_addEquiv_compactSupportSheafCohomology_two_inverseImage_of_twist`
also carries `(g⁻¹ s₀)_*` to `s` for every endomorphism `s₀` of `F₀` and `s` of `Q` which `u₀`
intertwines over `k̄`. -/
theorem exists_addEquiv_compactSupportSheafCohomology_two_inverseImage_of_twist_natural
    (hm : IsUnit (m : kbar)) (F₀ : EtaleModules.{u, 0} (ZMod m) (Spec (.of k)))
    (Q : ModuleCat.{u + 1} (ZMod m)) [Finite Q] (B : Q ⟶ Q)
    (u₀ : (etaleModuleInverseImage.{u, 0} (ZMod m)
        (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k)))) kbar)).obj
          (etaleModuleConstantSheaf (ZMod m) Q (Spec (.of k))) ⟶
      (etaleModuleInverseImage.{u, 0} (ZMod m)
        (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k)))) kbar)).obj F₀) [IsIso u₀]
    (h₀ : u₀ ≫ (frobeniusBaseChangeTwist.{u, 0} (ZMod m) (Over.mk (𝟙 (Spec (.of k)))) kbar p q
          hcard).app F₀ =
      (frobeniusBaseChangeTwist.{u, 0} (ZMod m) (Over.mk (𝟙 (Spec (.of k)))) kbar p q hcard).app
          (etaleModuleConstantSheaf (ZMod m) Q (Spec (.of k))) ≫
        (etaleModuleDirectImage.{u, 0} (ZMod m)
          (geometricFrobeniusBaseChange (Over.mk (𝟙 (Spec (.of k)))) kbar p q hcard)).map
          ((etaleModuleInverseImage.{u, 0} (ZMod m)
            (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k)))) kbar)).map
            ((constantSheaf (Spec (.of k)).smallEtaleTopology
              (ModuleCat.{u + 1} (ZMod m))).map B)) ≫
        (etaleModuleDirectImage.{u, 0} (ZMod m)
          (geometricFrobeniusBaseChange (Over.mk (𝟙 (Spec (.of k)))) kbar p q hcard)).map u₀) :
    ∃ e : (compactSupportSheafCohomology (ZMod m) g (CompactificationOf.ofProper g) kbar 2).obj
        ((etaleModuleInverseImage.{u, 0} (ZMod m) g).obj F₀) ≃+ Q,
      (∀ t, e (((compactSupportSheafFrobenius (ZMod m) g (CompactificationOf.ofProper g) kbar p q
          hcard 2).app ((etaleModuleInverseImage.{u, 0} (ZMod m) g).obj F₀)).hom t) =
        (p ^ q : ℕ) • B.hom (e t)) ∧
      ∀ (s : Q ⟶ Q) (s₀ : F₀ ⟶ F₀),
        (etaleModuleInverseImage.{u, 0} (ZMod m)
            (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k)))) kbar)).map
            ((constantSheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} (ZMod m))).map s) ≫
            u₀ =
          u₀ ≫ (etaleModuleInverseImage.{u, 0} (ZMod m)
            (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k)))) kbar)).map s₀ →
        ∀ t, e (((compactSupportSheafCohomology (ZMod m) g (CompactificationOf.ofProper g) kbar
            2).map ((etaleModuleInverseImage.{u, 0} (ZMod m) g).map s₀)).hom t) = s.hom (e t) := by
  let Y₀ : Over (Spec (.of k)) := Over.mk (𝟙 (Spec (.of k)))
  let Z : Over (Spec (.of k)) := Over.mk g
  let i : Z ⟶ Y₀ := Over.homMk g (Category.comp_id g)
  let IZ := etaleModuleInverseImage.{u, 0} (ZMod m) (fieldBaseChangeProj Z kbar)
  let G := etaleModuleInverseImage.{u, 0} (ZMod m) i.left
  let c := etaleModuleBaseChangeUnitIso (ZMod m) (fieldBaseChangeProj Y₀ kbar)
    (fieldBaseChangeProj Z kbar) i.left (fieldBaseChangeMap i kbar)
    (fieldBaseChangeProj Z kbar ≫ i.left) rfl (fieldBaseChangeMap_comp_fst i kbar).symm
  let ν : etaleModuleDirectImage.{u, 0} (ZMod m) (geometricFrobeniusBaseChange Z kbar p q hcard) ⋙
      etaleModuleDirectImage.{u, 0} (ZMod m) (fieldBaseChangeMap i kbar) ≅
      etaleModuleDirectImage.{u, 0} (ZMod m) (fieldBaseChangeMap i kbar) ⋙
        etaleModuleDirectImage.{u, 0} (ZMod m) (geometricFrobeniusBaseChange Y₀ kbar p q hcard) :=
    etaleModuleDirectImageComp.{u, 0} (ZMod m) (geometricFrobeniusBaseChange Z kbar p q hcard)
        (fieldBaseChangeMap i kbar)
        (geometricFrobeniusBaseChange Z kbar p q hcard ≫ fieldBaseChangeMap i kbar) rfl ≪≫
      (etaleModuleDirectImageComp.{u, 0} (ZMod m) (fieldBaseChangeMap i kbar)
        (geometricFrobeniusBaseChange Y₀ kbar p q hcard)
        (geometricFrobeniusBaseChange Z kbar p q hcard ≫ fieldBaseChangeMap i kbar)
        (geometricFrobeniusBaseChange_comp_fieldBaseChangeMap i p q hcard kbar)).symm
  let Bs := (constantSheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} (ZMod m))).map B
  have hu := Adjunction.twist_relation_of_baseChange
    (etaleModuleInverseImage.{u, 0} (ZMod m) (fieldBaseChangeProj Y₀ kbar)) IZ G
    (etaleModuleInverseImageAdj.{u, 0} (ZMod m) (fieldBaseChangeMap i kbar)) c
    (etaleModuleDirectImage.{u, 0} (ZMod m) (geometricFrobeniusBaseChange Y₀ kbar p q hcard))
    (etaleModuleDirectImage.{u, 0} (ZMod m) (geometricFrobeniusBaseChange Z kbar p q hcard)) ν
    (frobeniusBaseChangeTwist.{u, 0} (ZMod m) Y₀ kbar p q hcard)
    (frobeniusBaseChangeTwist.{u, 0} (ZMod m) Z kbar p q hcard) (fun L => by
      have h := etaleModuleBaseChangeMap_comp_frobeniusBaseChangeTwist (ZMod m) i p q hcard kbar L
      rw [etaleModuleBaseChangeMap_app] at h
      exact h) u₀ Bs h₀
  let ε := etaleModuleExtensionByZeroIdIso (ZMod m) X
  have hγ := Adjunction.twist_relation_conj IZ
    (etaleModuleDirectImage.{u, 0} (ZMod m) (geometricFrobeniusBaseChange Z kbar p q hcard))
    (frobeniusBaseChangeTwist.{u, 0} (ZMod m) Z kbar p q hcard) (ε.app (G.obj F₀))
    (ε.app (G.obj (etaleModuleConstantSheaf (ZMod m) Q (Spec (.of k)))))
    (c.inv.app _ ≫ (etaleModuleInverseImage.{u, 0} (ZMod m) (fieldBaseChangeMap i kbar)).map u₀ ≫
      c.hom.app F₀) (G.map Bs)
    ((etaleModuleExtensionByZero.{u, 0} (ZMod m) (CompactificationOf.ofProper g).immersion).map
      (G.map Bs)) (ε.hom.naturality (G.map Bs)) hu
  obtain ⟨e₁, he₁, hn₁⟩ := exists_addEquiv_compactSupportSheafCohomology_of_twist_natural (ZMod m) g
    (CompactificationOf.ofProper g) kbar p q hcard
    (IZ.mapIso (ε.app (G.obj F₀)) ≪≫ (asIso (c.inv.app _ ≫ (etaleModuleInverseImage.{u, 0} (ZMod m)
      (fieldBaseChangeMap i kbar)).map u₀ ≫ c.hom.app F₀)).symm ≪≫
      IZ.mapIso (ε.app (G.obj (etaleModuleConstantSheaf (ZMod m) Q (Spec (.of k))))).symm)
    (G.map Bs) hγ 2
  let T := compactSupportSheafCohomology (ZMod m) g (CompactificationOf.ofProper g) kbar 2
  let π := compactSupportSheafFrobenius (ZMod m) g (CompactificationOf.ofProper g) kbar p q hcard 2
  let ι := inverseImageEtaleModuleConstantSheafIso.{u, 0} (ZMod m) Q g
  let Gg := etaleModuleInverseImage.{u, 0} (ZMod m) g
  let e₁' : T.obj (Gg.obj F₀) ≃+
      T.obj (Gg.obj (etaleModuleConstantSheaf (ZMod m) Q (Spec (.of k)))) := e₁
  have he₁' : ∀ x, e₁' ((π.app (Gg.obj F₀)).hom x) =
      (T.map (Gg.map Bs)).hom ((π.app _).hom (e₁' x)) := he₁
  let e₂ : T.obj (Gg.obj (etaleModuleConstantSheaf (ZMod m) Q (Spec (.of k)))) ≃+
      T.obj (etaleModuleConstantSheaf (ZMod m) Q X) := (T.mapIso ι).toLinearEquiv.toAddEquiv
  obtain ⟨c₀, hc₀, hbij⟩ := exists_constantTopCohomology_generator g kbar m p q hcard hm
  let Φ := AddEquiv.ofBijective _ (hbij Q)
  let Bx := (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod m))).map B
  have hnat : ∀ y, (T.map ι.hom).hom ((π.app _).hom y) = (π.app _).hom ((T.map ι.hom).hom y) :=
    fun y => congrArg (fun φ => φ.hom y) (π.naturality ι.hom).symm
  have hBs : ∀ (b : Q ⟶ Q) y, (T.map ι.hom).hom ((T.map (Gg.map ((constantSheaf
      (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} (ZMod m))).map b))).hom y) =
      (T.map ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod m))).map b)).hom
        ((T.map ι.hom).hom y) := fun b y => by
    have hι := (etaleModuleInverseImageConstantIso.{u, 0} (ZMod m) g).hom.naturality b
    dsimp only [Functor.comp_map] at hι
    exact congrArg (fun φ => φ.hom y) (show T.map _ ≫ T.map ι.hom = T.map ι.hom ≫ T.map _ from
      (T.map_comp _ _).symm.trans ((congrArg T.map hι).trans (T.map_comp _ _)))
  have hsurj : ∀ t, ∃ v, e₂ (e₁' t) = Φ v := fun t =>
    (hbij Q).2 ((T.map ι.hom).hom (e₁' t)) |>.imp fun _ hv => hv.symm
  refine ⟨(e₁'.trans e₂).trans Φ.symm, fun t => Φ.injective ?_, fun s s₀ hs t => ?_⟩
  swap
  · let I' := etaleModuleInverseImage.{u, 0} (ZMod m) (fieldBaseChangeMap i kbar)
    let Bss := (constantSheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} (ZMod m))).map s
    have hw : IZ.map (G.map Bss) ≫ (c.inv.app _ ≫ I'.map u₀ ≫ c.hom.app F₀) =
        (c.inv.app _ ≫ I'.map u₀ ≫ c.hom.app F₀) ≫ IZ.map (G.map s₀) := by
      have h1 := c.inv.naturality Bss
      have h2 := c.hom.naturality s₀
      simp only [Functor.comp_map] at h1 h2
      rw [reassoc_of% h1, Category.assoc, Category.assoc, ← h2, ← I'.map_comp_assoc,
        ← I'.map_comp_assoc, hs]
    have hwinv : IZ.map (G.map s₀) ≫ inv (c.inv.app _ ≫ I'.map u₀ ≫ c.hom.app F₀) =
        inv (c.inv.app _ ≫ I'.map u₀ ≫ c.hom.app F₀) ≫ IZ.map (G.map Bss) := by
      rw [IsIso.comp_inv_eq, Category.assoc, hw, IsIso.inv_hom_id_assoc]
    have hε₁ : IZ.map ((etaleModuleExtensionByZero.{u, 0} (ZMod m) (𝟙 X)).map (G.map s₀)) ≫
        IZ.map (ε.hom.app (G.obj F₀)) =
        IZ.map (ε.hom.app (G.obj F₀)) ≫ IZ.map (G.map s₀) :=
      (IZ.map_comp _ _).symm.trans ((congrArg IZ.map (ε.hom.naturality (G.map s₀))).trans
        (IZ.map_comp _ _))
    have hε₂ : IZ.map (G.map Bss) ≫
        IZ.map (ε.inv.app (G.obj (etaleModuleConstantSheaf (ZMod m) Q (Spec (.of k))))) =
        IZ.map (ε.inv.app (G.obj (etaleModuleConstantSheaf (ZMod m) Q (Spec (.of k))))) ≫
          IZ.map ((etaleModuleExtensionByZero.{u, 0} (ZMod m) (𝟙 X)).map (G.map Bss)) :=
      (IZ.map_comp _ _).symm.trans ((congrArg IZ.map (ε.inv.naturality (G.map Bss))).trans
        (IZ.map_comp _ _))
    have hγs : IZ.map ((etaleModuleExtensionByZero.{u, 0} (ZMod m) (𝟙 X)).map (G.map s₀)) ≫
        (IZ.map (ε.hom.app (G.obj F₀)) ≫ inv (c.inv.app _ ≫ I'.map u₀ ≫ c.hom.app F₀) ≫
          IZ.map (ε.inv.app (G.obj (etaleModuleConstantSheaf (ZMod m) Q (Spec (.of k)))))) =
        (IZ.map (ε.hom.app (G.obj F₀)) ≫ inv (c.inv.app _ ≫ I'.map u₀ ≫ c.hom.app F₀) ≫
          IZ.map (ε.inv.app (G.obj (etaleModuleConstantSheaf (ZMod m) Q (Spec (.of k)))))) ≫
          IZ.map ((etaleModuleExtensionByZero.{u, 0} (ZMod m) (𝟙 X)).map (G.map Bss)) := by
      rw [reassoc_of% hε₁, reassoc_of% hwinv, hε₂]
      simp only [Category.assoc]
    have hn := hn₁ (G.map s₀) (G.map Bss) hγs t
    let Bxs := (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod m))).map s
    apply Φ.injective
    obtain ⟨v, hv'⟩ := hsurj t
    simp only [AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
    refine (congrArg e₂ hn).trans ?_
    change (T.map ι.hom).hom ((T.map (Gg.map Bss)).hom (e₁' t)) = _
    rw [hBs]
    change (T.map Bxs).hom (e₂ (e₁' t)) = _
    rw [hv', AddEquiv.symm_apply_apply]
    exact constantTopCohomologyMap_naturality g kbar m c₀ s v
  obtain ⟨v, hv'⟩ := hsurj t
  simp only [AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
  rw [he₁', hv', AddEquiv.symm_apply_apply, map_nsmul]
  change (T.map ι.hom).hom ((T.map (Gg.map Bs)).hom ((π.app _).hom (e₁' t))) = _
  rw [hBs, hnat]
  change (T.map Bx).hom ((π.app _).hom (e₂ (e₁' t))) = _
  rw [hv']
  change (T.map Bx).hom ((π.app _).hom (constantTopCohomologyMap g kbar m c₀ Q v)) =
    (p ^ q : ℕ) • constantTopCohomologyMap g kbar m c₀ Q (B.hom v)
  rw [compactSupportSheafFrobenius_constantTopCohomologyMap, hc₀, constantTopCohomologyMap_apply,
    map_nsmul, map_nsmul, ← constantTopCohomologyMap_apply]
  exact congrArg _ (constantTopCohomologyMap_naturality g kbar m c₀ B v)

end Stacks.EtaleCohomology

end
