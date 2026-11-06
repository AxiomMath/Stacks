module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LissePermutationDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveTopCohomologyCoverConstant

/-!
# `H²_c` of a lisse sheaf trivialized by a geometrically irreducible Galois cover

Let `X` be a smooth curve over a finite field `k` with a compactification, `x̄` a geometric point,
and `g : V ⟶ X` a connected finite étale cover, Galois (the stabilizers of its geometric fibre are
normal), with `V` geometrically irreducible over `k`. For every finite `ℤ/m`-module `M` with a
continuous action of `π₁(X, x̄)` on which the stabilizers act trivially, and `m` invertible in
`k`,

`#H²_c(X_k̄, ℱ_M) ≤ #M_{π₁(X, x̄)}`.

The functor `T = H²_c(X_k̄, ℱ_-)` is additive and preserves surjections
(`surjective_compactSupportSheafCohomology_two_lisseEtaleSheaf_map`); on the permutation module of
the fibre of `g` it is `H²_c(X_k̄, g_* ℤ/m) ≅ ℤ/m` (`nonempty_lisseEtaleSheaf_permModule_iso`,
`nonempty_linearEquiv_compactSupportSheafCohomology_two_directImage_constant`), and on `ℤ/m` it is
`H²_c(X_k̄, ℤ/m) ≅ ℤ/m` (the same for the trivial cover), so the counting argument of
[Stacks, Tag 03VK] (`finite_and_natCard_obj_le_natCard_coinvariants_of_perm`) applies.

The statements live in the standard model `HasDerivedCategory.standard` of the derived category, in
which `Stacks.EtaleCohomology.compactSupportSheafCohomology` is defined.

## Main results

* `surjective_compactSupportSheafCohomology_two_lisseEtaleSheaf_map`.
* `finite_and_natCard_compactSupportSheafCohomology_two_lisseEtaleSheaf_le_of_cover`.

## References

* [Stacks Project, Tag 03VK](https://stacks.math.columbia.edu/tag/03VK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.GroupCohomology

universe u

namespace Stacks.EtaleCohomology

/-! ### The kernel of a morphism of finite continuous modules -/

section Kernel

variable {G : Type (u + 1)} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (m : ℕ)
  [NeZero m] {P₀ P : FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod m) G} (b : P₀ ⟶ P)

/-- The action of `G` on the kernel of `b`. -/
def kernelRepresentation :
    Representation (ZMod m) G (LinearMap.ker b.hom.hom.hom.hom.hom) where
  toFun g := (P₀.obj.obj.obj.ρ g).asHom.hom.restrict fun x hx => by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [show b.hom.hom.hom.hom.hom ((P₀.obj.obj.obj.ρ g).asHom.hom x) =
        (P.obj.obj.obj.ρ g).asHom.hom (b.hom.hom.hom.hom.hom x) from
      ConcreteCategory.congr_hom (b.hom.hom.hom.comm g) x, hx, map_zero]
  map_one' := by
    ext ⟨x, hx⟩
    exact congrArg (fun f => f.asHom.hom x) (map_one P₀.obj.obj.obj.ρ)
  map_mul' g h := by
    ext ⟨x, hx⟩
    exact congrArg (fun f => f.asHom.hom x) (map_mul P₀.obj.obj.obj.ρ g h)

open scoped Stacks.DiscreteModuleTopology in
/-- **The kernel of a morphism of finite continuous modules**, with the restricted action. -/
def kernelContinuousModule : FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod m) G :=
  ⟨ofRepresentation (kernelRepresentation m b)
      ((isContinuous_actionOfRepresentation_iff _).2 fun x => by
        have h := isOpen_stabilizer (ZMod m) G P₀.obj x.1
        convert h using 1
        ext g
        exact Subtype.ext_iff),
    (moduleCat_isFG_iff_finite (ZMod m) _).2 (by
      have : Finite P₀.obj.obj.obj.V := (moduleCat_isFG_iff_finite (ZMod m) _).1 P₀.property
      exact Subtype.finite)⟩

/-- The inclusion of the kernel. -/
def kernelContinuousModuleι : kernelContinuousModule m b ⟶ P₀ :=
  finiteTypeContinuousModuleHomMk m (Submodule.subtype _) fun _ _ => rfl

end Kernel

/-! ### Surjectivity of `H²_c(X_k̄, ℱ_-)` -/

section Surjective

attribute [local instance] HasDerivedCategory.standard

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
  [IsAlgClosed kbar] (m : ℕ) [NeZero m]

/-- **`P ↦ H²_c(X_k̄, ℱ_P)` preserves surjections** on a curve. -/
theorem surjective_compactSupportSheafCohomology_two_lisseEtaleSheaf_map
    (hdim : topologicalKrullDim X.1 ≤ 1)
    {P₀ P : FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod m) (EtaleFundamentalGroup X.1 x)}
    (b : P₀ ⟶ P) (hb : Function.Surjective b.hom.hom.hom.hom.hom) :
    Function.Surjective ((compactSupportSheafCohomology (ZMod m) f j kbar 2).map
      ((lisseEtaleSheaf B X x (ZMod m)).map b)).hom := by
  have := (exact_lisseEtaleSheaf_map (B := B) (X := X) (x := x) (kernelContinuousModuleι m b) b
    (finiteTypeContinuousModule_hom_ext m fun (z : LinearMap.ker b.hom.hom.hom.hom.hom) =>
      LinearMap.mem_ker.1 z.2)
    hb (fun y hy => ⟨⟨y, hy⟩, rfl⟩)).2
  exact surjective_compactSupportSheafCohomology_two_map_of_epi f j kbar m hdim _

end Surjective

/-! ### The count -/

section Count

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1]
  {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [IsCurve k f] [Smooth f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
  [IsAlgClosed kbar] (m : ℕ) [NeZero m] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q)

include hcard in
/-- **`#H²_c(X_k̄, ℱ_M) ≤ #M_{π₁(X, x̄)}`** for a finite continuous module `M` trivialized by a
connected Galois finite étale cover `g : V ⟶ X` with `V` geometrically irreducible over `k`; in
particular `H²_c(X_k̄, ℱ_M)` is finite. -/
theorem finite_and_natCard_compactSupportSheafCohomology_two_lisseEtaleSheaf_le_of_cover
    (hm : IsUnit (m : kbar)) (hXgi : GeometricallyIrreducible f)
    {V : B.Scheme} [ConnectedSpace V.1] (g : V ⟶ X) [IsFinite (B.inclusion.map g)]
    [Etale (B.inclusion.map g)] (y : GeometricPoint V.1)
    (hgi : GeometricallyIrreducible (g.hom ≫ f))
    (hg : finiteEtale g.hom)
    (hN : (MulAction.stabilizer (EtaleFundamentalGroup X.1 (y.map g.hom))
      (finiteEtaleOverSourcePoint hg y)).Normal)
    [CompactSpace (EtaleFundamentalGroup X.1 (y.map g.hom))]
    (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod m)
      (EtaleFundamentalGroup X.1 (y.map g.hom)))
    (hM : ∀ s ∈ MulAction.stabilizer (EtaleFundamentalGroup X.1 (y.map g.hom))
      (finiteEtaleOverSourcePoint hg y), ∀ v, (M.obj.obj.obj.ρ s).asHom.hom v = v) :
    Finite ((compactSupportSheafCohomology (ZMod m) f j kbar 2).obj
        ((lisseEtaleSheaf B X (y.map g.hom) (ZMod m)).obj M)) ∧
    Nat.card ((compactSupportSheafCohomology (ZMod m) f j kbar 2).obj
        ((lisseEtaleSheaf B X (y.map g.hom) (ZMod m)).obj M)) ≤
      Nat.card
        (Representation.Coinvariants (finiteTypeContinuousModuleRepresentation (ZMod m) _ M)) := by
  let Λ := ZMod m
  let T := lisseEtaleSheaf B X (y.map g.hom) Λ ⋙ compactSupportSheafCohomology Λ f j kbar 2
  have : (lisseEtaleSheaf B X (y.map g.hom) Λ).Additive := by
    have : (finiteTypeLocallyConstantModuleSheafEquivalence B X (y.map g.hom) Λ).inverse.Additive :=
      Equivalence.additive_functor'
        (finiteTypeLocallyConstantModuleSheafEquivalence B X (y.map g.hom) Λ).symm
    have := Equivalence.additive_functor' (SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} Λ))
    dsimp only [lisseEtaleSheaf, lisseSheaf]
    infer_instance
  have : (compactSupportSheafCohomology Λ f j kbar 2).Additive := by
    have := additive_liftSingle Λ X.1 (fun _ => ⟨0, inferInstance⟩)
    dsimp only [compactSupportSheafCohomology, sheafSingleComplex]
    infer_instance
  have : T.Additive := inferInstanceAs (Functor.Additive (_ ⋙ _))
  have hdim : topologicalKrullDim X.1 ≤ 1 :=
    (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)).le
  have hT : ∀ {P Q : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup X.1 (y.map g.hom))} (b : P ⟶ Q),
      Function.Surjective b.hom.hom.hom.hom.hom → Function.Surjective (T.map b).hom :=
    fun b hb => surjective_compactSupportSheafCohomology_two_lisseEtaleSheaf_map B X
      (y.map g.hom) f j kbar m hdim b hb
  have : Finite ((finiteEtaleFiberFunctor (y.map g.hom)).obj (finiteEtaleOverSource hg)) :=
    finite_finiteEtaleFiber _ _
  let : Fintype ((finiteEtaleFiberFunctor (y.map g.hom)).obj (finiteEtaleOverSource hg)) :=
    Fintype.ofFinite _
  have hY : ∀ z : (finiteEtaleFiberFunctor (y.map g.hom)).obj (finiteEtaleOverSource hg),
      IsOpen (MulAction.stabilizer (EtaleFundamentalGroup X.1 (y.map g.hom)) z :
        Set (EtaleFundamentalGroup X.1 (y.map g.hom))) :=
    fun z => EtaleFundamentalGroup.isOpen_coe_of_isOpenSubgroup ⟨_, z, rfl⟩
  have : ConnectedSpace (finiteEtaleOverSource hg).left := inferInstanceAs (ConnectedSpace V.1)
  have htrans : ∀ z, ∃ σ : EtaleFundamentalGroup X.1 (y.map g.hom),
      σ • finiteEtaleOverSourcePoint hg y = z :=
    exists_smul_eq_of_connectedSpace_left _ _
  have : IsFinite g.hom := inferInstanceAs (IsFinite (B.inclusion.map g))
  have : Etale g.hom := inferInstanceAs (Etale (B.inclusion.map g))
  -- `T` on the permutation module of the fibre
  obtain ⟨i₁⟩ := nonempty_lisseEtaleSheaf_permModule_iso B g y m hg hY
  obtain ⟨i₂⟩ := nonempty_lisseEtaleSheaf_trivialContinuousModule_iso B V y m
  obtain ⟨C⟩ := nonempty_coverCompactification k f j.toBase j.immersion
    (CompactificationOf.immersion_toBase j) g.hom
  obtain ⟨e₃⟩ := nonempty_linearEquiv_compactSupportSheafCohomology_two_directImage_constant f j
    kbar m p q hcard C hm
    (C.geometricallyIrreducible_j_comp_q (CompactificationOf.immersion_toBase j) hgi)
  let eY : T.obj (permModule m PUnit.{u + 2} hY) ≃ₗ[Λ] Λ :=
    ((compactSupportSheafCohomology Λ f j kbar 2).mapIso
      (i₁ ≪≫ (etaleModuleDirectImage.{u, 0} Λ g.hom).mapIso i₂)).toLinearEquiv.trans e₃
  -- `T` on `ℤ/m`
  obtain ⟨i₃⟩ := nonempty_lisseEtaleSheaf_trivialContinuousModule_iso B X (y.map g.hom) m
  obtain ⟨C₁⟩ := nonempty_coverCompactification k f j.toBase j.immersion
    (CompactificationOf.immersion_toBase j) (𝟙 X.1)
  obtain ⟨e₄⟩ := nonempty_linearEquiv_compactSupportSheafCohomology_two_directImage_constant f j
    kbar m p q hcard C₁ hm
    (C₁.geometricallyIrreducible_j_comp_q (CompactificationOf.immersion_toBase j)
      (by rwa [Category.id_comp]))
  let e₁ : T.obj (trivialContinuousModule m) ≃ₗ[Λ] Λ :=
    ((compactSupportSheafCohomology Λ f j kbar 2).mapIso
      (i₃ ≪≫ ((etaleModuleDirectImageIdIso Λ X.1).app _).symm)).toLinearEquiv.trans e₄
  have : Finite (T.obj (permModule m PUnit.{u + 2} hY)) := Finite.of_equiv _ eY.toEquiv.symm
  have hcard' : Nat.card (T.obj (permModule m PUnit.{u + 2} hY)) ≤
      Nat.card (T.obj (trivialContinuousModule m)) :=
    (Nat.card_congr (eY.toEquiv.trans e₁.toEquiv.symm)).le
  exact finite_and_natCard_obj_le_natCard_coinvariants_of_perm m T hT hY htrans hN M hM hcard' e₁

end Count

end Stacks.EtaleCohomology
