module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.IntegralTransform
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.ArtinSchreierLevelSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseSheafStalkLinear
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.NeighborhoodsStalksPoints.StalksTestMaps
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.PointFiber
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.SmallEtaleSitePresentation
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.EtaleFundamental.FundamentalGroupTheorem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FundamentalGroupLocallyConstant.GeometricFibre

/-!
# The Artin–Schreier kernel is étale-locally free of rank one

Let `Λ` be a finite commutative ring. A sheaf of `Λ`-modules on the small étale site of a scheme
`Y` which is locally constant of finite type is étale-locally free of finite rank as soon as its
stalks at all geometric points are free: over a member `V` of a trivializing covering the sheaf is
constant with some value `E`, and if `V` is nonempty, `E` is the stalk at a geometric point of `V`
(members with empty source are dropped from the covering). The stalk of the lisse sheaf `ℱ_P` is
`P` as a `Λ`-module (`Stacks.EtaleCohomology.lisseEtaleSheafModuleFiberIso`), so `ℱ_P` is
étale-locally free when `P` is free; in particular the Artin–Schreier sheaf `L_ψ(g)` with
coefficients in `Λ` is. This is what makes tensoring with the kernel of the Fourier transform
exact, and what the projection formula for `Rf_!` asks of it.

If `g = h^q - h` for some `h ∈ A`, the Artin–Schreier cover has the section `t ↦ h`; a torsor
cover with a section has trivial character (`π₁` acts trivially on the one-point fibre of the
trivial cover and its action commutes with the section), so `L_ψ(g)` is the constant sheaf `Λ`.
For `g = 0` this is `L_ψ(0) ≅ Λ`, the restriction of the Fourier kernel to the antidiagonal.

## Main results

* `Stacks.EtaleCohomology.isLocallyFreeEtaleModule_of_forall_sheafFiber`
* `Stacks.EtaleCohomology.isLocallyFreeEtaleModule_lisseEtaleSheaf`
* `Stacks.ArtinSchreier.isLocallyFreeEtaleModule_artinSchreierLevelSheaf`
* `AlgebraicGeometry.TorsorCover.character_eq_one_of_hom_terminalCover`
* `Stacks.ArtinSchreier.nonempty_artinSchreierLevelSheaf_iso_constantSheaf_of_sub_eq`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.GroupCohomology

universe u

namespace AlgebraicGeometry.TorsorCover

variable {X : Scheme.{u}} [ConnectedSpace X] {K : Type*} [AddCommGroup K] (T : TorsorCover X K)

/-- **A torsor cover with a section has trivial character**: `π₁` fixes the image of the unique
point of the fibre of the trivial cover, hence acts trivially on the fibre. -/
public theorem character_eq_one_of_hom_terminalCover (sec : terminalCover X ⟶ T.cover)
    (x : GeometricPoint X) (p₀ : (finiteEtaleFiberFunctor x).obj T.cover) :
    T.character x p₀ = 1 := by
  ext σ
  let pt : (finiteEtaleFiberFunctor x).obj (terminalCover X) := ⟨x.hom, Category.comp_id _⟩
  let q := (finiteEtaleFiberFunctor x).map sec pt
  have hq : σ • q = (finiteEtaleFiberFunctor x).map (T.τ 0) q := by
    rw [T.τ_zero, CategoryTheory.Functor.map_id]
    show σ • q = q
    refine (ConcreteCategory.congr_hom (σ.hom.naturality sec) pt).trans ?_
    exact congrArg (fun z => (finiteEtaleFiberFunctor x).map sec z) (Subsingleton.elim _ pt)
  rw [← ofAdd_toAdd (T.character x p₀ σ), T.character_eq_of_smul x p₀ σ q hq]
  rfl

end AlgebraicGeometry.TorsorCover

namespace Stacks.EtaleCohomology

attribute [local instance] ModuleCat.hasLimitsOfSize

variable (Λ : Type) [CommRing Λ]

/-- **A locally constant sheaf of finite type whose geometric stalks are free of finite rank is
étale-locally free of finite rank.** -/
theorem isLocallyFreeEtaleModule_of_forall_sheafFiber {Y : Scheme.{u}}
    (N : EtaleModules.{u, 0} Λ Y)
    (hN : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ Y.smallEtaleTopology N)
    (hfib : ∀ s : GeometricPoint Y,
      Module.Free Λ (((Scheme.pointSmallEtale s.hom).sheafFiber
          (A := ModuleCat.{u + 1} Λ)).obj N) ∧
        Module.Finite Λ (((Scheme.pointSmallEtale s.hom).sheafFiber
          (A := ModuleCat.{u + 1} Λ)).obj N)) :
    IsLocallyFreeEtaleModule Λ N := by
  intro U
  obtain ⟨I, V, f, hcov, htriv⟩ := hN U
  refine ⟨{ i : I // Nonempty (V i).left }, fun i => V i.1, fun i => f i.1, ?_, fun i => ?_⟩
  · rw [Scheme.ofArrows_mem_smallEtaleTopology_iff] at hcov ⊢
    refine Set.eq_univ_of_forall fun u => ?_
    obtain ⟨i, w, hw⟩ := Set.mem_iUnion.1 (hcov ▸ Set.mem_univ u)
    exact Set.mem_iUnion.2 ⟨⟨i, ⟨w⟩⟩, w, hw⟩
  · obtain ⟨E, -, ⟨e⟩⟩ := htriv i.1
    obtain ⟨w⟩ := i.2
    let s : GeometricPoint Y := ((V i.1).left.algClosedPoint w).map (V i.1).hom
    let y : (Scheme.pointSmallEtale s.hom).fiber.obj (V i.1) :=
      Over.homMk ((V i.1).left.algClosedPoint w).hom rfl
    have : ∀ V' : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over V')
        (ModuleCat.{u + 1} Λ) := fun V' =>
      have := Stacks.ConstantSheaf.hasSheafify_moduleCat.{u + 1, u, 0, u + 1}
        (Y.smallEtaleTopology.over V') Λ
      inferInstance
    have : ∀ V' : Y.Etale, (Y.smallEtaleTopology.over V').WEqualsLocallyBijective
        (ModuleCat.{u + 1} Λ) := fun _ =>
      Stacks.ConstantSheaf.wEqualsLocallyBijective_moduleCat.{u, u + 1, u + 1, 0} _ Λ
    have : PreservesFilteredColimitsOfSize.{u + 1, u + 1} (forget (ModuleCat.{u + 1} Λ)) :=
      comp_preservesFilteredColimits (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
        (forget AddCommGrpCat.{u + 1})
    let l := (Stacks.ConstantSheaf.sheafFiberIsoOfConstantOver
      (Scheme.pointSmallEtale s.hom) y N E e).toLinearEquiv
    obtain ⟨hfree, hfin⟩ := hfib s
    exact ⟨E, ⟨Module.Free.of_equiv l, Module.Finite.equiv l⟩, ⟨e⟩⟩

variable [Finite Λ] (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1]
  (x : GeometricPoint X.1)

/-- **The lisse sheaf of a free finite `Λ`-module is étale-locally free of finite rank.** -/
theorem isLocallyFreeEtaleModule_lisseEtaleSheaf
    (P : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x))
    (hP : Module.Free Λ P.obj.obj.obj.V) :
    IsLocallyFreeEtaleModule Λ ((lisseEtaleSheaf B X x Λ).obj P) := by
  refine isLocallyFreeEtaleModule_of_forall_sheafFiber Λ _ ?_ fun s => ?_
  · exact (SmallEtale.isFiniteTypeLocallyConstant_sheafEquiv_functor_iff B X Λ _).2
      ((finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).inverse.obj P).property
  · obtain ⟨t⟩ := nonempty_finiteEtaleFiberFunctorIso_of_connectedSpace X.1 s x
    let l := (lisseEtaleSheafModuleFiberIso B X x Λ t P).toLinearEquiv
    have : Module.Finite Λ P.obj.obj.obj.V := (ModuleCat.isFG_iff _).1 P.property
    exact ⟨Module.Free.of_equiv l.symm, Module.Finite.equiv l.symm⟩

end Stacks.EtaleCohomology

namespace Stacks.ArtinSchreier

open Stacks.EtaleCohomology

variable (k : Type u) [Field k] [Fintype k] (A : Type u) [CommRing A] [Algebra k A] (g : A)
  [ConnectedSpace (Spec (.of A))] (Λ : Type) [CommRing Λ] [Finite Λ] (ψ : AddChar k Λ)
  (B : BigEtaleSite.{u}) (hX : schemeSizeBelow B.cutoff (Spec (.of A)))

/-- **T4 (a): the Artin–Schreier sheaf `L_ψ(g)` with coefficients in the finite commutative ring
`Λ` is étale-locally free of rank one.** -/
theorem isLocallyFreeEtaleModule_artinSchreierLevelSheaf (x : GeometricPoint (Spec (.of A)))
    (p₀ : (finiteEtaleFiberFunctor x).obj (cover k A g)) :
    IsLocallyFreeEtaleModule Λ (artinSchreierLevelSheaf k A g Λ ψ B hX x p₀) :=
  have : ConnectedSpace (specObject A B hX).1 := inferInstanceAs (ConnectedSpace (Spec (.of A)))
  isLocallyFreeEtaleModule_lisseEtaleSheaf Λ B (specObject A B hX) x _
    (Module.Free.of_equiv (ULift.moduleEquiv (R := Λ)).symm)

omit [ConnectedSpace (Spec (.of A))] in
/-- The section `t ↦ h` of the Artin–Schreier cover `t^q - t = g` when `g = h^q - h`. -/
def coverSection (h : A) (hg : h ^ Fintype.card k - h = g) : terminalCover (Spec (.of A)) ⟶
    cover k A g :=
  let φ : Ring k g →ₐ[A] A := AdjoinRoot.liftAlgHom (poly k g) (Algebra.ofId A A) h (by
    rw [poly, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_add,
      Polynomial.eval₂_X, Polynomial.eval₂_C, ← hg]
    change h ^ Fintype.card k - (h + (h ^ Fintype.card k - h)) = 0
    ring)
  MorphismProperty.Over.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext a
    exact φ.commutes a)

omit [Finite Λ] in
/-- **The Artin–Schreier character of `h^q - h` is trivial.** -/
theorem artinSchreierCharacter_eq_one_of_sub_eq (h : A) (hg : h ^ Fintype.card k - h = g)
    (x : GeometricPoint (Spec (.of A))) (p₀ : (finiteEtaleFiberFunctor x).obj (cover k A g)) :
    artinSchreierCharacter k A g ψ x p₀ = 1 := by
  rw [artinSchreierCharacter, (torsorCover k A g).character_eq_one_of_hom_terminalCover
    (coverSection k A g h hg) x p₀, inv_one, MonoidHom.comp_one]

/-- **T4 (e): the Artin–Schreier sheaf of `h^q - h` is the constant sheaf `Λ`**; in particular
`L_ψ(0) ≅ Λ`. -/
theorem nonempty_artinSchreierLevelSheaf_iso_constantSheaf_of_sub_eq (h : A)
    (hg : h ^ Fintype.card k - h = g) (x : GeometricPoint (Spec (.of A)))
    (p₀ : (finiteEtaleFiberFunctor x).obj (cover k A g)) :
    Nonempty (artinSchreierLevelSheaf k A g Λ ψ B hX x p₀ ≅
      etaleModuleConstantSheaf Λ (ModuleCat.of Λ (ULift.{u + 1} Λ)) (Spec (.of A))) :=
  have : ConnectedSpace (specObject A B hX).1 := inferInstanceAs (ConnectedSpace (Spec (.of A)))
  nonempty_lisseEtaleSheaf_iso_constantSheaf_of_trivial B (specObject A B hX) x Λ _ fun σ => by
    refine ModuleCat.hom_ext (LinearMap.ext fun v => ?_)
    show ((artinSchreierCharacter k A g ψ x p₀ σ : Λˣ) : Λ) • v = v
    have h1 : artinSchreierCharacter k A g ψ x p₀ σ = 1 := by
      rw [artinSchreierCharacter_eq_one_of_sub_eq k A g Λ ψ h hg x p₀, MonoidHom.one_apply]
    rw [h1, Units.val_one, one_smul]

end Stacks.ArtinSchreier

end
