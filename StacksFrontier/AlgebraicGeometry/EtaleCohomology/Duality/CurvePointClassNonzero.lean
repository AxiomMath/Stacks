module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.PointClassNonzero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CurvePointDuality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CurvePoincareDuality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CompactSupportTopExcision
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoverCompactification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseCompactSupportZero
public import StacksFrontier.AlgebraicGeometry.Chow.PrincipalDivisorPushforward.GenericallyFinite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ProperCompactSupportComparison

/-!
# The class of a point of a smooth curve is nonzero in `H²_c`

Let `k` be an algebraically closed field, `ℓ` a prime invertible in `k` and `Λ = ℤ/ℓ`. For a
smooth irreducible curve `W` over `k` with a compactification `j : W → X̄` and a `k`-point
`i : P → N` closed in an open `n : N → W`, some class `γ₀` supported at `P` and some
`z : Λ_X̄ → (n ≫ j)_! i_* Λ_P` have `z ∘ (n ≫ j)_! γ₀ ≠ 0` in `H²_c(W) = Ext²_X̄(Λ, j_! Λ_W)`
(`Stacks.EtaleCohomology.curvePointClassNonzero`).

## Main results

* `Stacks.EtaleCohomology.nontrivial_ext_two_extensionByZero_of_smoothProperCurve`:
  `H²(Y, j_! Λ_W) ≠ 0` for an open `W` of a smooth proper curve `Y` whose complement consists of
  closed points.
* `Stacks.EtaleCohomology.subsingleton_ext_extensionByZeroOfRestriction_extensionByZero`:
  `Ext^m_X̄(V_! Λ_V, j_! Λ_W) = 0` for `m > 1` when `V` meets `W` but misses a point of `W`.
* `Stacks.EtaleCohomology.nontrivial_ext_two_extensionByZero_of_curve`: `H²_c(W) ≠ 0` for a
  smooth irreducible curve `W`.
* `Stacks.EtaleCohomology.curvePointClassNonzero`: the class of a point is nonzero in `H²_c`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

open ExtensionTorsor

attribute [local instance] HasDerivedCategory.standard

attribute [-instance] AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- A space whose points have closed images under a continuous injection is `T1`. -/
private theorem t1Space_of_injective_of_isClosed_singleton {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {g : X → Y} (hg : Function.Injective g) (hc : Continuous g)
    (h : ∀ x, IsClosed ({g x} : Set Y)) : T1Space X := by
  refine ⟨fun x => ?_⟩
  have e : g ⁻¹' {g x} = {x} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact hg.eq_iff
  rw [← e]
  exact (h x).preimage hc

/-- The target of a continuous map with dense range from an irreducible space is irreducible. -/
private theorem irreducibleSpace_of_continuous_of_dense_range {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [IrreducibleSpace X] {g : X → Y} (hc : Continuous g)
    (hd : Dense (Set.range g)) : IrreducibleSpace Y := by
  refine (irreducibleSpace_def _).2 ?_
  have h := ((IrreducibleSpace.isIrreducible_univ X).image g hc.continuousOn).closure
  rwa [Set.image_univ, hd.closure_eq] at h

/-- An embedding of a space of smaller Krull dimension is not surjective. -/
private theorem exists_notMem_range_of_topologicalKrullDim_lt {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {g : X → Y} (hg : Topology.IsEmbedding g)
    (hlt : topologicalKrullDim X < topologicalKrullDim Y) : ∃ y, y ∉ Set.range g := by
  by_contra! h
  have h1 : topologicalKrullDim X = topologicalKrullDim (Set.range g) :=
    hg.toHomeomorph.isHomeomorph.topologicalKrullDim_eq
  rw [Set.eq_univ_of_forall h, (Homeomorph.Set.univ Y).isHomeomorph.topologicalKrullDim_eq] at h1
  exact hlt.ne h1

section SmoothProper

variable {k : Type u} [Field k] [IsAlgClosed k] {Y W : Scheme.{u}} (q : Y ⟶ Spec (.of k))
  [IsCurve k q] [Smooth q] [IsProper q] (j : W ⟶ Y) [IsOpenImmersion j]

include q in
/-- **`H²(Y, j_! Λ_W) ≠ 0`** for an open `j : W → Y` of a smooth proper curve over an algebraically
closed field whose complement consists of closed points. -/
theorem nontrivial_ext_two_extensionByZero_of_smoothProperCurve (hℓ : IsUnit (ℓ : k))
    (hcl : ∀ y : Y, y ∉ Set.range j.base → IsClosed ({y} : Set Y)) :
    Nontrivial (Ext (unitSheaf (X := Y) ℓ)
      ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) j).obj (unitSheaf (X := W) ℓ)) 2) := by
  have hp : ℓ.Prime := Fact.out
  have : NeZero ℓ := ⟨hp.ne_zero⟩
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian q
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace q
  have : IsNoetherian Y := ⟨⟩
  let Zc : TopologicalSpace.Closeds Y := ⟨(Set.range j.base)ᶜ,
    j.isOpenEmbedding.isOpen_range.isClosed_compl⟩
  let D := Scheme.IdealSheafData.vanishingIdeal Zc
  let ιZ : D.subscheme ⟶ Y := D.subschemeι
  have hrange : Set.range ιZ.base = (Set.range j.base)ᶜ := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have : TopologicalSpace.NoetherianSpace (CompactificationOf.ofProper q).space :=
    (inferInstance : TopologicalSpace.NoetherianSpace Y)
  obtain ⟨h, hS⟩ := shortExact_etaleModuleExtensionByZero_directImage (ZMod ℓ) ιZ j
    (by rw [hrange, compl_compl]) (unitSheaf (X := Y) ℓ)
  have : T1Space D.subscheme := t1Space_of_injective_of_isClosed_singleton
    ιZ.isClosedEmbedding.injective ιZ.base.hom.continuous fun x => hcl _ (hrange.subset ⟨x, rfl⟩)
  have hvan₀ : Subsingleton (Ext (unitSheaf (X := Y) ℓ)
      ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) (𝟙 Y)).obj
        ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) ιZ).obj
          ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) ιZ).obj (unitSheaf (X := Y) ℓ)))) 2) :=
    subsingleton_ext_extensionByZero_directImage_of_closed (ℓ := ℓ)
      (CompactificationOf.ofProper q) ιZ 0
      (by exact_mod_cast Stacks.Chow.topologicalKrullDim_nonpos_of_t1Space D.subscheme)
      ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) ιZ).obj (unitSheaf (X := Y) ℓ)) 2 (by norm_num)
  have hvan : Subsingleton (Ext (unitSheaf (X := Y) ℓ)
      ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) ιZ).obj
        ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) ιZ).obj (unitSheaf (X := Y) ℓ))) 2) :=
    @Function.Surjective.subsingleton _ _ _ hvan₀
      (Stacks.ExtAdjunction.postcomp_mk₀_bijective_of_isIso
        ((etaleModuleExtensionByZeroIdIso (ZMod ℓ) Y).app _).hom 2).2
  have hY2 : Nat.card (Ext (unitSheaf (X := Y) ℓ) (unitSheaf (X := Y) ℓ) 2) = ℓ :=
    natCard_ext_two_unitSheaf q hℓ
  have : Finite (Ext (unitSheaf (X := Y) ℓ) (unitSheaf (X := Y) ℓ) 2) :=
    Nat.finite_of_card_ne_zero (by rw [hY2]; exact hp.ne_zero)
  have : Nontrivial (Ext (unitSheaf (X := Y) ℓ) (unitSheaf (X := Y) ℓ) 2) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hY2]; exact hp.one_lt)
  have hsurj : Function.Surjective (fun x₁ : Ext (unitSheaf (X := Y) ℓ)
      ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) j).obj
        ((etaleModuleRestriction.{u, 0} (ZMod ℓ) j).obj (unitSheaf (X := Y) ℓ))) 2 =>
      x₁.comp (Ext.mk₀ ((etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) j).counit.app
        (unitSheaf (X := Y) ℓ))) (add_zero 2)) := fun x₂ =>
    Ext.covariant_sequence_exact₂ (unitSheaf (X := Y) ℓ) hS x₂ (@Subsingleton.elim _ hvan _ _)
  have : Nontrivial (Ext (unitSheaf (X := Y) ℓ) ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) j).obj
      ((etaleModuleRestriction.{u, 0} (ZMod ℓ) j).obj (unitSheaf (X := Y) ℓ))) 2) := by
    obtain ⟨a, b, hab⟩ := exists_pair_ne (Ext (unitSheaf (X := Y) ℓ) (unitSheaf (X := Y) ℓ) 2)
    obtain ⟨a', rfl⟩ := hsurj a
    obtain ⟨b', rfl⟩ := hsurj b
    exact ⟨⟨a', b', fun h => hab (by rw [h])⟩⟩
  exact (Stacks.ExtAdjunction.postcomp_mk₀_bijective_of_isIso (X := unitSheaf (X := Y) ℓ)
    ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) j).map
      (unitSheafIsoRestrictionOfIsOpenImmersion (ℓ := ℓ) j).inv) 2).1.nontrivial

end SmoothProper

/-- An irreducible separated scheme of finite type and dimension at most one over a field which
is not proper is affine. -/
private theorem isAffine_of_irreducibleSpace_of_not_isProper {k : Type u} [Field k] {X : Scheme.{u}}
    (g : X ⟶ Spec (.of k)) [IrreducibleSpace X] [IsSeparated g] [LocallyOfFiniteType g]
    [QuasiCompact g] (hdim : topologicalKrullDim X ≤ 1) (hg : ¬ IsProper g) : IsAffine X := by
  refine
    Stacks.AffineNoProperComponent.isAffine_of_topologicalKrullDim_le_one_of_forall_not_isProper
      k g hdim fun Z _ hP ↦ hg ?_
  have hZ : Z.1 = Set.univ :=
    Set.eq_univ_of_univ_subset (Z.2.2 (IrreducibleSpace.isIrreducible_univ _) (Set.subset_univ _))
  have : Surjective (Stacks.AffineNoProperComponent.componentIdealSheafData Z).subschemeι := by
    rw [surjective_iff, ← Set.range_eq_univ,
      Stacks.AffineNoProperComponent.range_subschemeι_componentIdealSheafData, hZ]
  have : UniversallyClosed g := UniversallyClosed.of_comp_surjective
    (Stacks.AffineNoProperComponent.componentIdealSheafData Z).subschemeι g
  exact ⟨⟩

/-- A nonempty open `U` of an irreducible scheme separated over `S`, missing some point, is not
proper over `S`. -/
private theorem not_isProper_ι_comp_of_notMem {X S : Scheme.{u}} [IrreducibleSpace X] (g : X ⟶ S)
    [IsSeparated g] (U : X.Opens) (hne : (U : Set X).Nonempty) (x : X) (hx : x ∉ U) :
    ¬ IsProper (U.ι ≫ g) := by
  intro _
  have : IsProper U.ι := IsProper.of_comp U.ι g
  have : PreconnectedSpace X :=
    ⟨(IrreducibleSpace.isIrreducible_univ _).isPreirreducible.isPreconnected⟩
  have huniv : (U : Set X) = Set.univ := IsClopen.eq_univ
    ⟨by simpa only [Scheme.Opens.range_ι] using U.ι.isClosedMap.isClosed_range, U.isOpen⟩ hne
  exact hx (show x ∈ (U : Set X) from huniv ▸ Set.mem_univ x)

section Closure

attribute [local instance] moduleCat_hasLimitsOfSize

variable {k : Type u} [Field k] [IsAlgClosed k] {W : Scheme.{u}} {f : W ⟶ Spec (.of k)}
  [LocallyOfFiniteType f] [QuasiCompact f] (jc : CompactificationOf (Over.mk f))

omit [IsAlgClosed k] [LocallyOfFiniteType f] in
/-- **Transport of `Ext`-vanishing to `X̄`**: for an open `V ⊆ X̄`, the vanishing of
`Ext^m_{V''}(Λ, (t_! Λ_W)|_{V''})` on `V'' = V ∩ W̄` gives `Ext^m_X̄(V_! Λ_V, j_! Λ_W) = 0`. -/
private theorem subsingleton_ext_extensionByZeroOfRestriction_extensionByZero_of_closure
    (V : jc.space.Opens) (m : ℕ)
    (h0 : Subsingleton (Ext (unitSheaf (X := (jc.closedSpaceι (𝟙 W) ⁻¹ᵁ V).toScheme) ℓ)
      ((etaleModuleRestriction.{u, 0} (ZMod ℓ) (jc.closedSpaceι (𝟙 W) ⁻¹ᵁ V).ι).obj
        ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) (jc.closedImmersion (𝟙 W)).toImage).obj
          (unitSheaf (X := W) ℓ))) m)) :
    Subsingleton (Ext ((etaleModuleExtensionByZeroOfRestriction.{u, 0} (ZMod ℓ) V.ι).obj
        (unitSheaf (X := jc.space) ℓ))
      ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj
        (unitSheaf (X := W) ℓ)) m) := by
  have hp : ℓ.Prime := Fact.out
  have : NeZero ℓ := ⟨hp.ne_zero⟩
  let t := (jc.closedImmersion (𝟙 W)).toImage
  let ι : jc.closedSpace (𝟙 W) ⟶ jc.space := jc.closedSpaceι (𝟙 W)
  have : @IsClosedImmersion _ jc.space ι :=
    (inferInstance : IsClosedImmersion (jc.closedSpaceι (𝟙 W)))
  have : @IsIntegralHom _ jc.space ι := (inferInstance : IsIntegralHom (jc.closedSpaceι (𝟙 W)))
  have sq : IsPullback (𝟙 W) t jc.immersion ι := jc.isPullback_restrictClosed (𝟙 W)
  have := etaleModuleInverseImage_preservesFiniteLimits.{u, 0} (ZMod ℓ) ι
  have := etaleModuleInverseImage_preservesFiniteColimits.{u, 0} (ZMod ℓ) ι
  have : PreservesFiniteColimits (etaleModuleDirectImage.{u, 0} (ZMod ℓ) ι) :=
    etaleModuleDirectImage_preservesFiniteColimits_of_isIntegralHom (ZMod ℓ) ι
  let V'' : (jc.closedSpace (𝟙 W)).Opens := ι ⁻¹ᵁ V
  let eM : (etaleModuleInverseImage.{u, 0} (ZMod ℓ) (ι ∣_ V)).obj
      ((etaleModuleRestriction.{u, 0} (ZMod ℓ) V.ι).obj (unitSheaf (X := jc.space) ℓ)) ≅
        unitSheaf (X := V''.toScheme) ℓ :=
    (etaleModuleInverseImage.{u, 0} (ZMod ℓ) (ι ∣_ V)).mapIso
        (unitSheafIsoRestrictionOfIsOpenImmersion (ℓ := ℓ) V.ι).symm ≪≫
      (etaleModuleInverseImageConstantIso.{u, 0} (ZMod ℓ) (ι ∣_ V)).app
        (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ)))
  have h1 := @Function.Surjective.subsingleton _ _ _ h0
    (Stacks.ExtAdjunction.precomp_mk₀_bijective_of_isIso eM.hom m).2
  have h2 := @Function.Surjective.subsingleton _ _ _ h1
    (Stacks.ExtAdjunction.extMap_bijective (etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) V''.ι)
      _ ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) t).obj (unitSheaf (X := W) ℓ)) m).2
  let eA := (etaleModuleInverseImageExtensionByZeroIso.{u, 0} (ZMod ℓ)
    (isPullback_morphismRestrict ι V)).app
      ((etaleModuleRestriction.{u, 0} (ZMod ℓ) V.ι).obj (unitSheaf (X := jc.space) ℓ))
  have h3 := @Function.Surjective.subsingleton _ _ _ h2
    (Stacks.ExtAdjunction.precomp_mk₀_bijective_of_isIso eA.inv m).2
  have h4 : Subsingleton (Ext ((etaleModuleExtensionByZeroOfRestriction.{u, 0} (ZMod ℓ) V.ι).obj
        (unitSheaf (X := jc.space) ℓ)) ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) ι).obj
          ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) t).obj (unitSheaf (X := W) ℓ))) m) :=
    ⟨fun a b => (Stacks.ExtAdjunction.extMap_bijective
      (etaleModuleInverseImageAdj.{u, 0} (ZMod ℓ) ι) _ _ m).1 (@Subsingleton.elim _ h3 _ _)⟩
  let eB : (etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj (unitSheaf (X := W) ℓ) ≅
      (etaleModuleDirectImage.{u, 0} (ZMod ℓ) ι).obj
        ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) t).obj (unitSheaf (X := W) ℓ)) :=
    (etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).mapIso
        ((etaleModuleDirectImageIdIso (ZMod ℓ) W).app _).symm ≪≫
      (etaleModuleExtensionByZeroDirectImageIso.{u, 0} (ZMod ℓ) (𝟙 W) t jc.immersion ι sq).app _
  exact @Function.Surjective.subsingleton _ _ _ h4
    (Stacks.ExtAdjunction.postcomp_mk₀_bijective_of_isIso eB.inv m).2

omit [LocallyOfFiniteType f] in
/-- **`Ext^m_X̄(V_! Λ_V, j_! Λ_W) = 0` for `m > 1`** when `W` is irreducible of dimension at most
one and the open `V ⊆ X̄` meets `W` but misses a point of `W`. -/
theorem subsingleton_ext_extensionByZeroOfRestriction_extensionByZero [IrreducibleSpace W]
    (hdimW : topologicalKrullDim W ≤ 1) (V : jc.space.Opens) (x : W)
    (hx : jc.immersion.base x ∉ V) (w : W) (hw : jc.immersion.base w ∈ V) (m : ℕ) (hm : 1 < m) :
    Subsingleton (Ext ((etaleModuleExtensionByZeroOfRestriction.{u, 0} (ZMod ℓ) V.ι).obj
        (unitSheaf (X := jc.space) ℓ))
      ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj
        (unitSheaf (X := W) ℓ)) m) := by
  have : IsLocallyNoetherian jc.space := LocallyOfFiniteType.isLocallyNoetherian jc.toBase
  have : CompactSpace jc.space := QuasiCompact.compactSpace_of_compactSpace jc.toBase
  have : IsNoetherian jc.space := ⟨⟩
  let t := (jc.closedImmersion (𝟙 W)).toImage
  let ι : jc.closedSpace (𝟙 W) ⟶ jc.space := jc.closedSpaceι (𝟙 W)
  have : @IsClosedImmersion _ jc.space ι :=
    (inferInstance : IsClosedImmersion (jc.closedSpaceι (𝟙 W)))
  have sq : IsPullback (𝟙 W) t jc.immersion ι := jc.isPullback_restrictClosed (𝟙 W)
  have : TopologicalSpace.NoetherianSpace (jc.closedSpace (𝟙 W)) :=
    ι.isClosedEmbedding.isInducing.noetherianSpace
  have hιt : ∀ y : W, ι.base (t.base y) = jc.immersion.base y := fun y => by
    rw [← Scheme.Hom.comp_apply, ← sq.w, Category.id_comp]
  have hdense : Dense (Set.range t.base) := t.denseRange
  have : IrreducibleSpace (jc.closedSpace (𝟙 W)) :=
    irreducibleSpace_of_continuous_of_dense_range t.base.hom.continuous hdense
  have hdimZ : topologicalKrullDim (jc.closedSpace (𝟙 W)) ≤ 1 := by
    have : TopologicalSpace.NoetherianSpace (jc.restrictClosed (𝟙 W)).space :=
      (inferInstance : TopologicalSpace.NoetherianSpace (jc.closedSpace (𝟙 W)))
    have h1 := topologicalKrullDim_le_of_isOpen_of_dense k _ (jc.restrictClosed (𝟙 W)).toBase _
      t.isOpenEmbedding.isOpen_range hdense
    have h2 : topologicalKrullDim (Set.range t.base) = topologicalKrullDim W :=
      ((t.isOpenEmbedding.isEmbedding.toHomeomorph).isHomeomorph.topologicalKrullDim_eq).symm
    exact h1.trans (h2 ▸ hdimW)
  let V'' : (jc.closedSpace (𝟙 W)).Opens := ι ⁻¹ᵁ V
  have hV''ne : (V'' : Set (jc.closedSpace (𝟙 W))).Nonempty :=
    ⟨t.base w, show ι.base (t.base w) ∈ V from (hιt w).symm ▸ hw⟩
  have : IrreducibleSpace V''.toScheme :=
    Subtype.irreducibleSpace ⟨hV''ne,
      (IrreducibleSpace.isIrreducible_univ _).isPreirreducible.open_subset V''.isOpen
        (Set.subset_univ _)⟩
  have hdim'' : topologicalKrullDim V''.toScheme ≤ 1 :=
    (AlgebraicGeometry.topologicalKrullDim_le_of_etale V''.ι).trans hdimZ
  have : TopologicalSpace.NoetherianSpace V''.toScheme :=
    V''.ι.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact (V''.ι ≫ ι ≫ jc.toBase) :=
    ⟨fun _ _ _ => TopologicalSpace.NoetherianSpace.isCompact _⟩
  have : IsSeparated V''.ι := AlgebraicGeometry.IsSeparated.isSeparated_of_mono V''.ι
  have : IsSeparated (V''.ι ≫ ι ≫ jc.toBase) := inferInstance
  have : LocallyOfFiniteType (V''.ι ≫ ι ≫ jc.toBase) := inferInstance
  have : IsAffine V''.toScheme := isAffine_of_irreducibleSpace_of_not_isProper _ hdim''
    (not_isProper_ι_comp_of_notMem (ι ≫ jc.toBase) V'' hV''ne (t.base x)
      fun h => hx (hιt x ▸ (h : ι.base (t.base x) ∈ V)))
  exact subsingleton_ext_extensionByZeroOfRestriction_extensionByZero_of_closure jc V m
    (subsingleton_ext_unitSheaf_of_isAffine_of_curve (V''.ι ≫ ι ≫ jc.toBase) hdim'' _ m hm)

end Closure

section Curve

variable {k : Type u} [Field k] [IsAlgClosed k] {W : Scheme.{u}} (f : W ⟶ Spec (.of k))
  [SmoothOfRelativeDimension 1 f] [TopologicalSpace.NoetherianSpace W] [IrreducibleSpace W]
  (jc : CompactificationOf (Over.mk f))

include jc in
omit [IsAlgClosed k] in
/-- A smooth irreducible noetherian scheme of relative dimension one over `k` with a
compactification is a curve. -/
theorem isCurve_of_compactification : IsCurve k f := by
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have : ConnectedSpace W :=
    connectedSpace_iff_univ.2 (IrreducibleSpace.isIrreducible_univ W).isConnected
  have : IsIntegral W := Stacks.Chow.isIntegral_of_connectedSpace_of_smooth f
  have : IsSeparated f := by
    rw [← CompactificationOf.immersion_toBase jc]
    infer_instance
  have : QuasiCompact f := ⟨fun _ _ _ => TopologicalSpace.NoetherianSpace.isCompact _⟩
  exact (isCurve_iff k f).2 ⟨IsVariety.mk,
    by exact_mod_cast topologicalKrullDim_eq_of_smoothOfRelativeDimension f 1⟩

/-- **`H²_c(W) ≠ 0`** for a smooth irreducible curve `W` over an algebraically closed field,
computed through any compactification `j : W → X̄`. -/
theorem nontrivial_ext_two_extensionByZero_of_curve (hℓ : IsUnit (ℓ : k)) :
    Nontrivial (Ext (unitSheaf (X := jc.space) ℓ)
      ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj
        (unitSheaf (X := W) ℓ)) 2) := by
  have hp : ℓ.Prime := Fact.out
  have : NeZero ℓ := ⟨hp.ne_zero⟩
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have : ConnectedSpace W :=
    connectedSpace_iff_univ.2 (IrreducibleSpace.isIrreducible_univ W).isConnected
  have : IsCurve k f := isCurve_of_compactification f jc
  have hjU : jc.immersion ≫ jc.toBase = f := CompactificationOf.immersion_toBase jc
  obtain ⟨C⟩ := nonempty_coverCompactification k f jc.toBase jc.immersion hjU (𝟙 W)
  have hjq : C.j ≫ C.q = f := by
    rw [← C.hq, ← Category.assoc, C.w, Category.id_comp, hjU]
  let jc₂ : CompactificationOf (Over.mk f) :=
    ⟨StructuredArrow.mk (Y := Over.mk C.q)
      (Over.homMk (U := Over.mk f) (V := Over.mk C.q) C.j hjq),
      ⟨(inferInstance : IsOpenImmersion C.j), (inferInstance : IsProper C.q)⟩⟩
  have : IsOpenImmersion jc₂.immersion := (inferInstance : IsOpenImmersion C.j)
  obtain ⟨e⟩ := nonempty_ext_addEquiv_of_compactifications ℓ f jc jc₂ (unitSheaf (X := W) ℓ) 2
  have : Nontrivial (Ext (unitSheaf (X := jc₂.space) ℓ)
      ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc₂.immersion).obj (unitSheaf (X := W) ℓ)) 2) :=
    nontrivial_ext_two_extensionByZero_of_smoothProperCurve C.q C.j hℓ C.isClosed_compl
  exact e.symm.injective.nontrivial

end Curve

section Main

/-- **The point class from an excision open**: an open `V ⊆ X̄` cutting `i(P)` out of `n(N)`,
covering `X̄` together with `n(N)`, meeting `W` but missing a point of `W`, yields the point class
`Stacks.EtaleCohomology.PointClassNonzeroAt`. -/
private theorem pointClassNonzeroAt_of_opens {k : Type u} [Field k] [IsAlgClosed k]
    (hℓ : IsUnit (ℓ : k)) {W : Scheme.{u}} (f : W ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 f]
    [TopologicalSpace.NoetherianSpace W] [IrreducibleSpace W] (jc : CompactificationOf (Over.mk f))
    {N P : Scheme.{u}} (n : N ⟶ W) [IsOpenImmersion n] (i : P ⟶ N) [IsClosedImmersion i]
    (V : jc.space.Opens)
    (hi : Set.range (i ≫ n ≫ jc.immersion).base =
      Set.range (n ≫ jc.immersion).base \ (V : Set jc.space))
    (htop : V ⊔ (n ≫ jc.immersion).opensRange = ⊤) (x : W) (hx : jc.immersion.base x ∉ V)
    (w : W) (hw : jc.immersion.base w ∈ V) :
    PointClassNonzeroAt ℓ 1 f jc n i := by
  have hp : ℓ.Prime := Fact.out
  have : NeZero ℓ := ⟨hp.ne_zero⟩
  have : QuasiCompact f := ⟨fun _ _ _ => TopologicalSpace.NoetherianSpace.isCompact _⟩
  have hW1 : topologicalKrullDim W ≤ 1 := by
    rw [topologicalKrullDim_eq_of_smoothOfRelativeDimension f 1]
    norm_num
  obtain ⟨S, hS, ⟨e₁'⟩, ⟨e₂'⟩, ⟨e₃'⟩⟩ := exists_shortExact_extensionByZero_sup_stratum (ZMod ℓ) V
    (n ≫ jc.immersion) i hi (unitSheaf (X := jc.space) ℓ)
  rw [htop] at e₂'
  have := isIso_etaleModuleExtensionByZeroAdj_counit_app_top (ZMod ℓ) (unitSheaf (X := jc.space) ℓ)
  let eY : S.X₂ ≅ unitSheaf (X := jc.space) ℓ := e₂' ≪≫
    asIso ((etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) (⊤ : jc.space.Opens).ι).counit.app
      (unitSheaf (X := jc.space) ℓ))
  let eC : S.X₃ ≅ (etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) (n ≫ jc.immersion)).obj
      ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := P) ℓ)) :=
    e₃' ≪≫ (etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) (n ≫ jc.immersion)).mapIso
      ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).mapIso
        (unitSheafRestrictionIdInverseImageIso (ℓ := ℓ) (i ≫ n ≫ jc.immersion)))
  have hvan := subsingleton_ext_extensionByZeroOfRestriction_extensionByZero (ℓ := ℓ) jc hW1 V
    x hx w hw 2 (by norm_num)
  have h₁ := @Function.Surjective.subsingleton _ _ _ hvan
    (Stacks.ExtAdjunction.precomp_mk₀_bijective_of_isIso e₁'.hom 2).2
  have := nontrivial_ext_two_extensionByZero_of_curve (ℓ := ℓ) f jc hℓ
  obtain ⟨zz, hzz⟩ := exists_ne (0 : Ext (unitSheaf (X := jc.space) ℓ)
    ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj (unitSheaf (X := W) ℓ)) 2)
  obtain ⟨x₂, hx₂⟩ := (Stacks.ExtAdjunction.precomp_mk₀_bijective_of_isIso eY.inv 2).2 zz
  obtain ⟨x₃, hx₃⟩ := Ext.contravariant_sequence_exact₂ hS _ x₂ (@Subsingleton.elim _ h₁ _ _)
  obtain ⟨γ₀, hγ₀⟩ := (Stacks.ExtAdjunction.extMap_bijective
    (etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) (n ≫ jc.immersion)) _
    ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj (unitSheaf (X := W) ℓ))
    (2 * 1)).2 ((Ext.mk₀ eC.inv).comp x₃ (zero_add 2))
  refine ⟨γ₀, Ext.mk₀ (eY.inv ≫ S.g ≫ eC.hom), ?_⟩
  rw [hγ₀]
  have hxw : (Ext.mk₀ (eY.inv ≫ S.g ≫ eC.hom)).comp ((Ext.mk₀ eC.inv).comp x₃ (zero_add 2))
      (zero_add 2) = zz := by
    rw [← hx₂, ← hx₃]
    change (Ext.mk₀ (eY.inv ≫ S.g ≫ eC.hom)).comp ((Ext.mk₀ eC.inv).comp x₃ (zero_add 2))
      (zero_add 2) = (Ext.mk₀ eY.inv).comp ((Ext.mk₀ S.g).comp x₃ (zero_add 2)) (zero_add 2)
    rw [Ext.mk₀_comp_mk₀_assoc, Ext.mk₀_comp_mk₀_assoc, Category.assoc, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  exact hxw ▸ hzz

variable (ℓ) in
/-- **The class of a point of a smooth curve is nonzero in `H²_c`**: for `k` algebraically closed
and `ℓ` invertible in `k`, `Stacks.EtaleCohomology.CurvePointClassNonzero ℓ k` holds. -/
theorem curvePointClassNonzero (k : Type u) [Field k] [IsAlgClosed k] (hℓ : IsUnit (ℓ : k)) :
    CurvePointClassNonzero ℓ k := by
  intro W f _ _ _ jc N P n _ i _ _ _
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have : QuasiCompact f := ⟨fun _ _ _ => TopologicalSpace.NoetherianSpace.isCompact _⟩
  have : TopologicalSpace.NoetherianSpace N := n.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact (n ≫ f) := ⟨fun _ _ _ => TopologicalSpace.NoetherianSpace.isCompact _⟩
  have : TopologicalSpace.NoetherianSpace P := (i ≫ n).isEmbedding.isInducing.noetherianSpace
  have : IsProper (i ≫ n ≫ f) :=
    isProper_of_smoothOfRelativeDimension_zero (i ≫ n ≫ f) ((jc.restrictOpen n).restrictClosed i)
  have hPcl : IsClosed (Set.range (i ≫ n ≫ jc.immersion).base) := by
    have : IsProper ((i ≫ n ≫ jc.immersion) ≫ jc.toBase) := by
      rw [Category.assoc, Category.assoc, CompactificationOf.immersion_toBase]
      infer_instance
    have : IsProper (i ≫ n ≫ jc.immersion) := IsProper.of_comp _ jc.toBase
    exact (i ≫ n ≫ jc.immersion).isClosedMap.isClosed_range
  let V : jc.space.Opens := ⟨(Set.range (i ≫ n ≫ jc.immersion).base)ᶜ, hPcl.isOpen_compl⟩
  have hmemV : ∀ y, y ∈ V ↔ y ∉ Set.range (i ≫ n ≫ jc.immersion).base := fun y => Iff.rfl
  have hsub : Set.range (i ≫ n ≫ jc.immersion).base ⊆ Set.range (n ≫ jc.immersion).base :=
    Set.range_subset_iff.2 fun p => ⟨i.base p, (Scheme.Hom.comp_apply i (n ≫ jc.immersion) p).symm⟩
  have hi : Set.range (i ≫ n ≫ jc.immersion).base =
      Set.range (n ≫ jc.immersion).base \ (V : Set jc.space) := by
    ext y
    exact ⟨fun hy => ⟨hsub hy, fun hyV => (hmemV y).1 hyV hy⟩,
      fun hy => not_not.1 ((hmemV y).not.1 hy.2)⟩
  have htop : V ⊔ (n ≫ jc.immersion).opensRange = ⊤ := by
    refine eq_top_iff.2 fun y _ => TopologicalSpace.Opens.mem_sup.2 ?_
    by_cases hy : y ∈ Set.range (i ≫ n ≫ jc.immersion).base
    · exact Or.inr (hsub hy)
    · exact Or.inl ((hmemV y).2 hy)
  obtain ⟨p₀⟩ := (inferInstance : IrreducibleSpace P).toNonempty
  have hx : jc.immersion.base (n.base (i.base p₀)) ∉ V := fun h =>
    (hmemV _).1 h ⟨p₀, by simp only [Scheme.Hom.comp_apply]⟩
  obtain ⟨w, hw⟩ := exists_notMem_range_of_topologicalKrullDim_lt (i ≫ n).isEmbedding (by
    rw [topologicalKrullDim_eq_of_smoothOfRelativeDimension (i ≫ n ≫ f) 0,
      topologicalKrullDim_eq_of_smoothOfRelativeDimension f 1]
    norm_num)
  refine pointClassNonzeroAt_of_opens (ℓ := ℓ) hℓ f jc n i V hi htop _ hx w ((hmemV _).2 ?_)
  rintro ⟨p, hp⟩
  refine hw ⟨p, jc.immersion.isOpenEmbedding.injective ?_⟩
  rwa [← Scheme.Hom.comp_apply, Category.assoc]

end Main

end Stacks.EtaleCohomology

end
