module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.FirstVanishing.GaloisCoverKilling

/-!
# A class of `H¹(X, M)` with finite constant coefficients is killed by a Galois cover

Let `X` be an irreducible, geometrically unibranch scheme with a geometric point `x` and let `M` be
a finite abelian group. Every class `ξ ∈ H¹(X, M)` of the constant sheaf `M` dies on some finite
étale Galois cover `Z ⟶ X` whose group has order dividing `|M|` and which has a point over `x`.

This is the statement of
`Stacks.EtaleCohomology.exists_finiteEtaleGaloisCover_mapExactFunctor_eq_zero`, which treats
`M = ℤ/dℤ`, for an arbitrary finite coefficient group, and the proof is the same: the class is
the boundary of a global section of the quotient of an injective presentation of `M`, the fibre
over that section is an `M`-torsor and a finite locally constant sheaf of sets, hence represented
on finite étale covers by a finite étale `Y ⟶ X` (Stacks 03RV), a connected component `A` of `Y`
is a Galois cover, and comparing automorphisms of `A` with the inclusion `A ⟶ Y` embeds `Aut A`
into `M`. It is the step of the proof of Stacks 0EYT that kills `ξ̄` by a Galois cover with group
`G ⊂ M`, without first decomposing `M` into cyclic groups.

## Main results

* `Stacks.EtaleCohomology.exists_finiteEtaleGaloisCover_mapExactFunctor_eq_zero_of_finite` — the
  statement above.

## References

* [Stacks Project, Tag 0EYT](https://stacks.math.columbia.edu/tag/0EYT)
* [Stacks Project, Tag 03AJ](https://stacks.math.columbia.edu/tag/03AJ)
* [Stacks Project, Tag 03RV](https://stacks.math.columbia.edu/tag/03RV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite AlgebraicGeometry

universe u

namespace CategoryTheory.PreGaloisCategory

/-- A connected subobject `ι : A ⟶ Y` with as many maps to `Y` as `Y` has fibre points is
Galois. -/
private theorem isGalois_of_mono_of_natCard_hom_eq {C : Type*} [Category* C] [GaloisCategory C]
    (F : C ⥤ FintypeCat) [FiberFunctor F] {A Y : C} [IsConnected A] (ι : A ⟶ Y) [Mono ι]
    (h : Nat.card (A ⟶ Y) = Nat.card (F.obj Y)) : IsGalois A := by
  have hιinj : Function.Injective (F.map ι) :=
    have : Mono (F.map ι) := F.map_mono ι
    ConcreteCategory.injective_of_mono_of_preservesPullback (F.map ι)
  rw [isGalois_iff_pretransitive F A]
  refine ⟨fun a₁ a₂ => ?_⟩
  obtain ⟨f, hf⟩ :=
    ((evaluation_injective_of_isConnected F A Y a₁).bijective_of_nat_card_le h.ge).2 (F.map ι a₂)
  have hpb : IsIso (pullback.fst f ι) := IsConnected.noTrivialComponent _ _
    fun hi => not_initial_of_inhabited F ((fiberPullbackEquiv F f ι).symm ⟨(a₁, a₂), hf⟩) hi
  let σ : A ⟶ A := inv (pullback.fst f ι) ≫ pullback.snd f ι
  have hσ : σ ≫ ι = f := by
    simp only [σ, Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]
  have hσa : F.map σ a₁ = a₂ := by
    apply hιinj
    show (F.map σ ≫ F.map ι) a₁ = _
    rwa [← F.map_comp, hσ]
  have : Nonempty (F.obj A) := ⟨a₁⟩
  have hsurj := surjective_of_nonempty_fiber_of_isConnected F σ
  have : IsIso (F.map σ) :=
    (ConcreteCategory.isIso_iff_bijective _).2 ⟨Finite.injective_iff_surjective.2 hsurj, hsurj⟩
  have : IsIso σ := isIso_of_reflects_iso σ F
  exact ⟨Aut.of (asIso σ), hσa⟩

end CategoryTheory.PreGaloisCategory

namespace Stacks.EtaleCohomology

attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

/-- A connected finite étale cover of an irreducible, geometrically unibranch scheme is
irreducible. -/
private theorem irreducibleSpace_left_of_isConnected {X : Scheme.{u}} [IrreducibleSpace X]
    (hX : IsGeometricallyUnibranch X) (B : FiniteEtaleOver X) [PreGaloisCategory.IsConnected B] :
    IrreducibleSpace ((finiteEtaleToEtale X).obj B).left :=
  have : ConnectedSpace ((finiteEtaleToEtale X).obj B).left :=
    connectedSpace_left_of_isConnected B inferInstance
  have : Etale ((finiteEtaleToEtale X).obj B).hom := ((finiteEtaleToEtale X).obj B).prop
  irreducibleSpace_of_etale_of_isGeometricallyUnibranch (X := X)
    ((finiteEtaleToEtale X).obj B).hom hX

section FiberTorsor

variable {X : Scheme.{u}} (S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
  (c : (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ S.X₃) (hS : S.ShortExact)

include hS in
/-- A finite étale cover through which every nonempty étale scheme with a section of the fibre
sheaf factors is nonempty. -/
private theorem nonempty_left_of_fiberSheaf [Nonempty X] {Y : FiniteEtaleOver X}
    (hY : ∀ W : X.Etale, Nonempty W.left → Nonempty ((fiberSheaf S c).obj.obj (op W)) →
      Nonempty Y.left) :
    Nonempty Y.left := by
  obtain ⟨R, hR, hne⟩ := Stacks.Cohomology.Torsors.fiberPseudoTorsor_isTorsor.{u + 1} S hS
    (boundaryPresheafSection S c) (etaleSiteTerminal X)
  by_contra hcon
  refine Scheme.bot_not_mem_smallEtaleTopology (T := etaleSiteTerminal X) (Classical.arbitrary X)
    (X.smallEtaleTopology.transitive hR ⊥ fun {V} g hg => ?_)
  rw [show (⊥ : Sieve (etaleSiteTerminal X)).pullback g = ⊥ from
    le_antisymm (fun _ _ hk => hk) bot_le]
  exact AlgebraicGeometry.smallEtale_bot_mem X
    (not_nonempty_iff.mp fun hV => hcon (hY V hV (hne hg)))

include hS in
/-- **The automorphisms of a connected subcover of the representing cover embed into `M`.** If
`Y` represents the fibre sheaf, an `M`-torsor, then for a mono `ι : A ⟶ Y` from an irreducible
cover, `σ ↦ (ι ∘ σ) - ι` embeds `Aut A` into `M`. -/
private theorem natCard_aut_dvd_natCard_of_bijective {M : AddCommGrpCat.{u + 1}} [Finite M]
    (e : S.X₁ ≅ (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M)
    {Y : FiniteEtaleOver X} (ν : (fiberSheaf S c).obj.obj (op ((finiteEtaleToEtale X).obj Y)))
    (hYbij : ∀ A : FiniteEtaleOver X, Function.Bijective
      (fun f : A ⟶ Y ↦ (fiberSheaf S c).obj.map ((finiteEtaleToEtale X).map f).op ν))
    {A : FiniteEtaleOver X} (ι : A ⟶ Y) [Mono ι]
    [IrreducibleSpace ((finiteEtaleToEtale X).obj A).left] :
    Nat.card (Aut A) ∣ Nat.card M := by
  let β : (A ⟶ Y) → (fiberSheaf S c).obj.obj (op ((finiteEtaleToEtale X).obj A)) :=
    fun f => (fiberSheaf S c).obj.map ((finiteEtaleToEtale X).map f).op ν
  have hβcomp : ∀ (g : A ⟶ A) (f : A ⟶ Y),
      β (g ≫ f) = (fiberSheaf S c).obj.map ((finiteEtaleToEtale X).map g).op (β f) := by
    intro g f
    simp only [β, Functor.map_comp, op_comp]
    rfl
  let χfun : Aut A → Multiplicative M := fun σ =>
    Multiplicative.ofAdd (diffConst S c hS e (β ι) (β (σ.asIso.hom ≫ ι)))
  have hχmul : ∀ σ τ : Aut A, χfun (σ * τ) = χfun σ * χfun τ := by
    intro σ τ
    have h : β ((σ * τ).asIso.hom ≫ ι) =
        (fiberSheaf S c).obj.map ((finiteEtaleToEtale X).map τ.asIso.hom).op
          (β (σ.asIso.hom ≫ ι)) := by
      show β ((τ.asIso.hom ≫ σ.asIso.hom) ≫ ι) = _
      rw [Category.assoc, hβcomp]
    simp only [χfun, ← ofAdd_add]
    congr 1
    rw [h, diffConst_add S c hS e (β ι) (β (τ.asIso.hom ≫ ι)), hβcomp τ.asIso.hom ι,
      diffConst_restrict, add_comm]
  let χ : Aut A →* Multiplicative M := MonoidHom.mk' χfun hχmul
  have hχinj : Function.Injective χ := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    have h0 : diffConst S c hS e (β ι) (β (σ.asIso.hom ≫ ι)) = 0 := by
      simpa [χ, χfun] using hσ
    have h : σ.asIso.hom ≫ ι = 𝟙 A ≫ ι := by
      rw [Category.id_comp]
      exact (hYbij A).1 (eq_of_diffConst_eq_zero S c hS e h0).symm
    exact Aut.ext (Iso.ext ((cancel_mono ι).1 h))
  have h := Subgroup.card_subgroup_dvd_card χ.range
  rw [← Nat.card_congr (MonoidHom.ofInjective hχinj).toEquiv] at h
  exact h.trans (Nat.card_congr Multiplicative.toAdd).dvd

end FiberTorsor

/-- **A class of `H¹(X, M)` with finite constant coefficients `M` is killed by a finite étale
Galois cover of order dividing `|M|`.** Let `X` be an irreducible, geometrically unibranch scheme,
`x` a geometric point, `M` a finite abelian group and `ξ ∈ H¹(X, M)` a class of the constant sheaf
`M`. There is a finite étale Galois cover `Z ⟶ X` with group `G` of order dividing `|M|`, with a
point over `x`, on which `ξ` dies. -/
theorem exists_finiteEtaleGaloisCover_mapExactFunctor_eq_zero_of_finite {X : Scheme.{u}}
    [IrreducibleSpace X] (hX : IsGeometricallyUnibranch X) (M : AddCommGrpCat.{u + 1})
    [Finite M]
    (ξ : Sheaf.H.{u + 1} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M) 1)
    (x : GeometricPoint X) :
    ∃ (G : Type u) (_ : Group G) (_ : Finite G), Nat.card G ∣ Nat.card M ∧
      ∃ (Z : FiniteEtaleGaloisCover X G) (z : Spec (.of x.residueField) ⟶ Z.obj.left),
        z ≫ Z.obj.hom = x.hom ∧
          ξ.mapExactFunctor (etaleAbelianInverseImage.{u, 0} Z.obj.hom) = 0 := by
  let IP : InjectivePresentation
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M) := Classical.arbitrary _
  let S := ShortComplex.mk IP.f (cokernel.π IP.f) (cokernel.condition IP.f)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel IP.f }
  have : Injective S.X₂ := IP.injective
  obtain ⟨c, hc⟩ := Stacks.Cohomology.Torsors.ext_one_boundary_surjective S hS _ ξ
  let e : S.X₁ ≅ (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M := Iso.refl _
  have := isFiniteLocallyConstant_fiberSheaf S c hS M e
  obtain ⟨Y, ν, hYbij, hYne⟩ :=
    exists_finiteEtaleOver_bijective_of_isFiniteLocallyConstant (fiberSheaf S c)
  let Fx := finiteEtaleFiberFintypeFunctor X x
  obtain ⟨y⟩ : Nonempty (Fx.obj Y) := by
    rw [← PreGaloisCategory.not_initial_iff_fiber_nonempty]
    exact fun hi => (isEmpty_left_of_isInitial_finiteEtaleOver Y hi).elim
      (nonempty_left_of_fiberSheaf S c hS hYne).some
  obtain ⟨A, ι, a, -, hAconn, hιmono⟩ := PreGaloisCategory.fiber_in_connected_component Fx Y y
  have hcard : ∀ (B : FiniteEtaleOver X) [PreGaloisCategory.IsConnected B], Nonempty (B ⟶ Y) →
      Nat.card (B ⟶ Y) = Nat.card M := by
    intro B _ ⟨f⟩
    have := irreducibleSpace_left_of_isConnected hX B
    rw [Nat.card_eq_of_bijective _ (hYbij B), natCard_fiberSheaf S c hS e
      ((fiberSheaf S c).obj.map ((finiteEtaleToEtale X).map f).op ν)]
  obtain ⟨B, b, hBgal, hBbij⟩ := PreGaloisCategory.exists_galois_representative Fx Y
  have hcardY : Nat.card (Fx.obj Y) = Nat.card M := by
    rw [← Nat.card_eq_of_bijective _ hBbij]
    exact hcard B ⟨(hBbij.2 y).choose⟩
  have := PreGaloisCategory.isGalois_of_mono_of_natCard_hom_eq Fx ι
    ((hcard A ⟨ι⟩).trans hcardY.symm)
  have := irreducibleSpace_left_of_isConnected hX A
  let a' : finiteEtaleFiber x A := a
  refine ⟨Aut A, inferInstance, inferInstance,
    natCard_aut_dvd_natCard_of_bijective S c hS e ν hYbij ι,
    FiniteEtaleGaloisCover.ofIsGalois A, a'.1, a'.2, ?_⟩
  have h := mapExactFunctor_eq_zero_of_fiberSheaf S c hS
    ((fiberSheaf S c).obj.map ((finiteEtaleToEtale X).map ι).op ν)
  rwa [hc] at h

end Stacks.EtaleCohomology

end
