module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FirstCohomologyKilling.FiniteEtaleCover
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.FirstFailureDiagram
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCover
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCoverSheets
public import StacksFrontier.AlgebraicGeometry.Properties.Unibranch
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.UnibranchLocallyIrreducible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.FirstVanishing.ConstantAbelianSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.FirstVanishing.GaloisObjectCover
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ModelBridges.FiniteEtaleRepresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.CoverCriterion
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.FirstCohomology

/-!
# A class of `H¹(X, ℤ/dℤ)` is killed by a finite étale Galois cover of order dividing `d`

Let `X` be an irreducible, geometrically unibranch scheme with a geometric point `x`. Every class
`ξ ∈ H¹(X, ℤ/dℤ)` dies on some finite étale Galois cover `Z ⟶ X` whose group has order dividing
`d` and which has a point over `x`. This is a step of the second proof of Stacks 0EYU.

The class `ξ` corresponds to a `ℤ/dℤ`-torsor: the fibre sheaf of an injective presentation
`0 ⟶ ℤ/dℤ ⟶ I ⟶ Q ⟶ 0` over a global section `c` of `Q` with `∂c = ξ`
(`Stacks.EtaleCohomology.fiberSheaf`). It is a finite locally constant sheaf of sets, hence
represented on finite étale covers by a finite étale cover `Y` of `X` (Stacks 03RV); a connected
component of `Y` is the Galois cover.

## Main definitions

* `Stacks.EtaleCohomology.constSection`: the constant section of `F₁ ≅ M̲` with a given value.
* `Stacks.EtaleCohomology.diffConst`: the constant of `M` by which two sections of the fibre sheaf
  over an irreducible étale scheme differ.

## Main results

* `Stacks.EtaleCohomology.natCard_fiberSheaf`: over an irreducible étale scheme with a section,
  the fibre sheaf has `Nat.card M` sections.
* `Stacks.EtaleCohomology.exists_finiteEtaleGaloisCover_mapExactFunctor_eq_zero`: the statement
  above.

## References

* [Stacks Project, Tag 0EYU](https://stacks.math.columbia.edu/tag/0EYU)
* [Stacks Project, Tag 03AJ](https://stacks.math.columbia.edu/tag/03AJ)
* [Stacks Project, Tag 03RV](https://stacks.math.columbia.edu/tag/03RV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite AlgebraicGeometry

universe u

namespace CategoryTheory.PreGaloisCategory

variable {C : Type*} [Category* C] [GaloisCategory C] (F : C ⥤ FintypeCat) [FiberFunctor F]

/-- A connected object `A` with a monomorphism into `Y` is Galois as soon as `A` has as many
morphisms to `Y` as `Y` has points in the fibre. -/
private theorem isGalois_of_mono_of_natCard_hom_eq {A Y : C} [IsConnected A] (ι : A ⟶ Y) [Mono ι]
    (h : Nat.card (A ⟶ Y) = Nat.card (F.obj Y)) : IsGalois A := by
  have hιinj : Function.Injective (F.map ι) := by
    have : Mono (F.map ι) := Functor.map_mono F ι
    exact ConcreteCategory.injective_of_mono_of_preservesPullback (F.map ι)
  rw [isGalois_iff_pretransitive F A]
  refine ⟨fun a₁ a₂ => ?_⟩
  have hbij : Function.Bijective (fun f : A ⟶ Y => F.map f a₁) :=
    (evaluation_injective_of_isConnected F A Y a₁).bijective_of_nat_card_le h.ge
  obtain ⟨f, hf⟩ := hbij.2 (F.map ι a₂)
  have hpb : IsIso (pullback.fst f ι) := IsConnected.noTrivialComponent _ _
    fun hi => not_initial_of_inhabited F ((fiberPullbackEquiv F f ι).symm ⟨(a₁, a₂), hf⟩) hi
  let σ' : A ⟶ A := inv (pullback.fst f ι) ≫ pullback.snd f ι
  have hσ' : σ' ≫ ι = f := by
    simp only [σ', Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]
  have hσa : F.map σ' a₁ = a₂ := hιinj <| by
    show (F.map σ' ≫ F.map ι) a₁ = _
    rw [← F.map_comp, hσ']
    exact hf
  have : Nonempty (F.obj A) := ⟨a₁⟩
  have hsurj := surjective_of_nonempty_fiber_of_isConnected F σ'
  have : IsIso (F.map σ') :=
    (ConcreteCategory.isIso_iff_bijective _).2 ⟨Finite.injective_iff_surjective.2 hsurj, hsurj⟩
  have : IsIso σ' := isIso_of_reflects_iso σ' F
  exact ⟨Aut.of (asIso σ'), hσa⟩

end CategoryTheory.PreGaloisCategory

namespace Stacks.EtaleCohomology

section FiberTorsor

variable {X : Scheme.{u}} (S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
  (c : (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ S.X₃)

section Constants

variable (hS : S.ShortExact) {M : AddCommGrpCat.{u + 1}}
  (e : S.X₁ ≅ (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M)

/-- The constant sections of `F₁ ≅ M̲` over `W`, as a map of abelian groups out of `M`. -/
def constSectionHom (W : X.Etale) : M ⟶ S.X₁.obj.obj (op W) :=
  Stacks.ConstantSheaf.constantSheafSection X.smallEtaleTopology _ M W ≫ e.inv.hom.app (op W)

/-- The constant section of `F₁ ≅ M̲` over `W` with value `k`. -/
abbrev constSection (W : X.Etale) (k : M) : S.X₁.obj.obj (op W) :=
  constSectionHom S e W k

/-- The constant section is additive in its value. -/
theorem constSection_add (W : X.Etale) (k k' : M) :
    constSection S e W (k + k') = constSection S e W k + constSection S e W k' :=
  map_add _ _ _

/-- The constant section with value `0` is `0`. -/
theorem constSection_zero (W : X.Etale) : constSection S e W 0 = 0 :=
  map_zero _

/-- The restriction along `W' ⟶ W` of the constant section with value `k` is the constant section
with value `k`. -/
theorem constSection_restrict {W W' : X.Etale} (g : W' ⟶ W) (k : M) :
    S.X₁.obj.map g.op (constSection S e W k) = constSection S e W' k := by
  have h : constSectionHom S e W ≫ S.X₁.obj.map g.op = constSectionHom S e W' := by
    simp only [constSectionHom, Category.assoc]
    rw [← e.inv.hom.naturality g.op, ← Category.assoc,
      Stacks.ConstantSheaf.constantSheafSection_restrict]
  exact ConcreteCategory.congr_hom h k

/-- Over an irreducible étale scheme `W`, every section of `F₁ ≅ M̲` is constant: `k ↦` the
constant section with value `k` is a bijection from `M` onto the sections over `W`. -/
theorem bijective_constSection (W : X.Etale) [IrreducibleSpace W.left] :
    Function.Bijective (constSection S e W) :=
  ((ConcreteCategory.bijective_of_isIso (e.inv.hom.app (op W)))).comp
    (Scheme.bijective_toSheafify_const_app_of_irreducibleSpace_addCommGrpCat M W)

include hS e

/-- Over an irreducible étale scheme, any two sections `s`, `t` of the fibre sheaf differ by the
action of a constant section. -/
theorem exists_constSection_fiberSheafAct {W : X.Etale} [IrreducibleSpace W.left]
    (s t : (fiberSheaf S c).obj.obj (op W)) :
    ∃ k : M, fiberSheafAct S c hS (constSection S e W k) s = t := by
  obtain ⟨a, ha⟩ := (bijective_fiberSheafAct S c hS s).2 t
  obtain ⟨k, rfl⟩ := (bijective_constSection S e W).2 a
  exact ⟨k, ha⟩

/-- **The difference of two sections of the fibre sheaf over an irreducible étale scheme**, a
constant of `M`. -/
def diffConst {W : X.Etale} [IrreducibleSpace W.left] (s t : (fiberSheaf S c).obj.obj (op W)) :
    M :=
  (exists_constSection_fiberSheafAct S c hS e s t).choose

/-- The constant section with value `diffConst s t` carries `s` to `t`. -/
theorem diffConst_spec {W : X.Etale} [IrreducibleSpace W.left]
    (s t : (fiberSheaf S c).obj.obj (op W)) :
    fiberSheafAct S c hS (constSection S e W (diffConst S c hS e s t)) s = t :=
  (exists_constSection_fiberSheafAct S c hS e s t).choose_spec

/-- A constant `k` whose constant section carries `s` to `t` is `diffConst s t`. -/
theorem eq_diffConst {W : X.Etale} [IrreducibleSpace W.left]
    {s t : (fiberSheaf S c).obj.obj (op W)} {k : M}
    (h : fiberSheafAct S c hS (constSection S e W k) s = t) : k = diffConst S c hS e s t :=
  (bijective_constSection S e W).1 ((bijective_fiberSheafAct S c hS s).1
    (h.trans (diffConst_spec S c hS e s t).symm))

/-- The difference constants are additive: `diffConst s r = diffConst s t + diffConst t r`. -/
theorem diffConst_add {W : X.Etale} [IrreducibleSpace W.left]
    (s t r : (fiberSheaf S c).obj.obj (op W)) :
    diffConst S c hS e s r = diffConst S c hS e s t + diffConst S c hS e t r := by
  refine (eq_diffConst S c hS e ?_).symm
  rw [constSection_add, fiberSheafAct_add, diffConst_spec, diffConst_spec]

/-- Two sections of the fibre sheaf whose difference constant is `0` are equal. -/
theorem eq_of_diffConst_eq_zero {W : X.Etale} [IrreducibleSpace W.left]
    {s t : (fiberSheaf S c).obj.obj (op W)} (h : diffConst S c hS e s t = 0) : s = t := by
  have := diffConst_spec S c hS e s t
  rwa [h, constSection_zero, fiberSheafAct_zero] at this

/-- The difference constant of two sections is unchanged by restriction along `W' ⟶ W` between
irreducible étale schemes. -/
theorem diffConst_restrict {W W' : X.Etale} [IrreducibleSpace W.left] [IrreducibleSpace W'.left]
    (g : W' ⟶ W) (s t : (fiberSheaf S c).obj.obj (op W)) :
    diffConst S c hS e ((fiberSheaf S c).obj.map g.op s) ((fiberSheaf S c).obj.map g.op t) =
      diffConst S c hS e s t := by
  refine (eq_diffConst S c hS e ?_).symm
  rw [← constSection_restrict S e g, ← fiberSheaf_map_fiberSheafAct, diffConst_spec]

/-- **Over an irreducible étale scheme with a section, the fibre sheaf has as many sections as
`M` has elements.** -/
theorem natCard_fiberSheaf {W : X.Etale} [IrreducibleSpace W.left]
    (s : (fiberSheaf S c).obj.obj (op W)) :
    Nat.card ((fiberSheaf S c).obj.obj (op W)) = Nat.card M := by
  refine Nat.card_eq_of_bijective (diffConst S c hS e s) ⟨fun t t' h => ?_, fun k => ?_⟩
  · refine eq_of_diffConst_eq_zero S c hS e ?_
    have := diffConst_add S c hS e s t t'
    rw [h] at this
    exact add_eq_left.1 this.symm
  · exact ⟨fiberSheafAct S c hS (constSection S e W k) s, (eq_diffConst S c hS e rfl).symm⟩

/-- **The difference characters of a component of a finite étale cover representing the fibre
sheaf.** If `Y` represents the fibre sheaf on finite étale covers via `ν` and `ι : A ⟶ Y` is a
monomorphism from a finite étale cover with irreducible total space, then `Aut A` embeds in `M`. -/
private theorem natCard_aut_dvd_natCard_of_bijective {A Y : FiniteEtaleOver X}
    [IrreducibleSpace ((finiteEtaleToEtale X).obj A).left]
    (ν : (fiberSheaf S c).obj.obj (op ((finiteEtaleToEtale X).obj Y)))
    (hYbij : ∀ B : FiniteEtaleOver X, Function.Bijective
      (fun f : B ⟶ Y ↦ (fiberSheaf S c).obj.map ((finiteEtaleToEtale X).map f).op ν))
    (ι : A ⟶ Y) [Mono ι] : Nat.card (Aut A) ∣ Nat.card M := by
  let β : ∀ B : FiniteEtaleOver X, (B ⟶ Y) → (fiberSheaf S c).obj.obj
      (op ((finiteEtaleToEtale X).obj B)) :=
    fun B f => (fiberSheaf S c).obj.map ((finiteEtaleToEtale X).map f).op ν
  have hβcomp : ∀ {B B' : FiniteEtaleOver X} (g : B' ⟶ B) (f : B ⟶ Y),
      β B' (g ≫ f) = (fiberSheaf S c).obj.map ((finiteEtaleToEtale X).map g).op (β B f) := by
    intro B B' g f
    simp only [β, Functor.map_comp, op_comp]
    rfl
  let s₀ := β A ι
  let χfun : Aut A → Multiplicative M := fun σ =>
    Multiplicative.ofAdd (diffConst S c hS e s₀ (β A (σ.asIso.hom ≫ ι)))
  have hχmul : ∀ σ τ : Aut A, χfun (σ * τ) = χfun σ * χfun τ := by
    intro σ τ
    have h1 : β A ((σ * τ).asIso.hom ≫ ι) =
        (fiberSheaf S c).obj.map ((finiteEtaleToEtale X).map τ.asIso.hom).op
          (β A (σ.asIso.hom ≫ ι)) := by
      show β A ((τ.asIso.hom ≫ σ.asIso.hom) ≫ ι) = _
      rw [Category.assoc, hβcomp]
    simp only [χfun, ← ofAdd_add]
    congr 1
    rw [h1, diffConst_add S c hS e s₀ (β A (τ.asIso.hom ≫ ι)), hβcomp τ.asIso.hom ι,
      diffConst_restrict,
      add_comm]
  let χ : Aut A →* Multiplicative M := MonoidHom.mk' χfun hχmul
  have hχinj : Function.Injective χ := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    have h0 : diffConst S c hS e s₀ (β A (σ.asIso.hom ≫ ι)) = 0 := by simpa [χ, χfun] using hσ
    have h2 : σ.asIso.hom ≫ ι = 𝟙 A ≫ ι := by
      rw [Category.id_comp]
      exact (hYbij A).1 (eq_of_diffConst_eq_zero S c hS e h0).symm
    exact Aut.ext (Iso.ext ((cancel_mono ι).1 h2))
  have h := Subgroup.card_subgroup_dvd_card χ.range
  rwa [← Nat.card_congr (MonoidHom.ofInjective hχinj).toEquiv] at h

end Constants

attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

/-- A finite étale cover `Y` representing the fibre sheaf on finite étale covers has nonempty
total space, as the fibre sheaf is locally nonempty. -/
private theorem nonempty_left_of_fiberSheaf [Nonempty X] (hS : S.ShortExact) {Y : FiniteEtaleOver X}
    (hYne : ∀ W : X.Etale, Nonempty W.left → Nonempty ((fiberSheaf S c).obj.obj (op W)) →
      Nonempty Y.left) : Nonempty Y.left := by
  obtain ⟨R, hR, hne⟩ := Stacks.Cohomology.Torsors.fiberPseudoTorsor_isTorsor.{u + 1} S hS
    (boundaryPresheafSection S c) (etaleSiteTerminal X)
  by_contra hcon
  refine Scheme.bot_not_mem_smallEtaleTopology (T := etaleSiteTerminal X)
    (Classical.arbitrary X) (X.smallEtaleTopology.transitive hR ⊥ fun {V} g hg => ?_)
  rw [show (⊥ : Sieve (etaleSiteTerminal X)).pullback g = ⊥ from
    le_antisymm (fun _ _ hk => hk) bot_le]
  exact AlgebraicGeometry.smallEtale_bot_mem X
    (not_nonempty_iff.1 fun hV => hcon (hYne V hV (hne hg)))

end FiberTorsor

attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

/-- **A class of `H¹(X, ℤ/dℤ)` is killed by a finite étale Galois cover of order dividing
`d`.** Let `X` be an irreducible, geometrically unibranch scheme, `x` a geometric point and
`ξ ∈ H¹(X, ℤ/dℤ)`. There is a finite étale Galois cover `Z ⟶ X` with group `G` of order dividing
`d`, with a point over `x`, on which `ξ` dies. -/
theorem exists_finiteEtaleGaloisCover_mapExactFunctor_eq_zero {X : Scheme.{u}}
    [IrreducibleSpace X] (hX : IsGeometricallyUnibranch X) (d : ℕ) (hd : 0 < d)
    (ξ : Sheaf.H.{u + 1} (FirstFailureDiagram.constantZMod X d) 1) (x : GeometricPoint X) :
    ∃ (G : Type u) (_ : Group G) (_ : Finite G), Nat.card G ∣ d ∧
      ∃ (Z : FiniteEtaleGaloisCover X G) (z : Spec (.of x.residueField) ⟶ Z.obj.left),
        z ≫ Z.obj.hom = x.hom ∧
          ξ.mapExactFunctor (etaleAbelianInverseImage.{u, 0} Z.obj.hom) = 0 := by
  have : NeZero d := ⟨hd.ne'⟩
  let M := AddCommGrpCat.of (ULift.{u + 1} (ZMod d))
  have hM : Nat.card M = d := by simp [M]
  let IP : InjectivePresentation (FirstFailureDiagram.constantZMod X d) := Classical.arbitrary _
  let S := ShortComplex.mk IP.f (cokernel.π IP.f) (cokernel.condition IP.f)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel IP.f }
  have : Injective S.X₂ := IP.injective
  obtain ⟨c, hc⟩ := Stacks.Cohomology.Torsors.ext_one_boundary_surjective S hS _ ξ
  let e : S.X₁ ≅ (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M := Iso.refl _
  have : Finite M := inferInstanceAs (Finite (ULift (ZMod d)))
  have := isFiniteLocallyConstant_fiberSheaf S c hS M e
  obtain ⟨Y, ν, hYbij, hYne⟩ :=
    exists_finiteEtaleOver_bijective_of_isFiniteLocallyConstant (fiberSheaf S c)
  let Fx := finiteEtaleFiberFintypeFunctor X x
  have : Nonempty X := ‹IrreducibleSpace X›.toNonempty
  have hYleft := nonempty_left_of_fiberSheaf S c hS hYne
  have hFxY : Nonempty (Fx.obj Y) := by
    rw [← PreGaloisCategory.not_initial_iff_fiber_nonempty]
    exact fun hi => (isEmpty_left_of_isInitial_finiteEtaleOver Y hi).elim hYleft.some
  obtain ⟨y⟩ := hFxY
  obtain ⟨A, ι, a, -, hAconn, hιmono⟩ := PreGaloisCategory.fiber_in_connected_component Fx Y y
  have hirr : ∀ (B : FiniteEtaleOver X) [PreGaloisCategory.IsConnected B],
      IrreducibleSpace ((finiteEtaleToEtale X).obj B).left := fun B _ =>
    have : ConnectedSpace ((finiteEtaleToEtale X).obj B).left :=
      connectedSpace_left_of_isConnected B inferInstance
    have : Etale ((finiteEtaleToEtale X).obj B).hom := ((finiteEtaleToEtale X).obj B).prop
    irreducibleSpace_of_etale_of_isGeometricallyUnibranch (X := X)
      ((finiteEtaleToEtale X).obj B).hom hX
  have hcard : ∀ (B : FiniteEtaleOver X) [PreGaloisCategory.IsConnected B], Nonempty (B ⟶ Y) →
      Nat.card (B ⟶ Y) = d := by
    intro B _ ⟨f⟩
    have := hirr B
    rw [Nat.card_eq_of_bijective _ (hYbij B), natCard_fiberSheaf S c hS e
      ((fiberSheaf S c).obj.map ((finiteEtaleToEtale X).map f).op ν), hM]
  obtain ⟨B, b, hBgal, hBbij⟩ := PreGaloisCategory.exists_galois_representative Fx Y
  have hcardY : Nat.card (Fx.obj Y) = d := by
    rw [← Nat.card_eq_of_bijective _ hBbij]
    exact hcard B ⟨(hBbij.2 y).choose⟩
  have := PreGaloisCategory.isGalois_of_mono_of_natCard_hom_eq Fx ι
    ((hcard A ⟨ι⟩).trans hcardY.symm)
  have := hirr A
  let a' : finiteEtaleFiber x A := a
  refine ⟨Aut A, inferInstance, inferInstance,
    hM ▸ natCard_aut_dvd_natCard_of_bijective S c hS e ν hYbij ι,
    FiniteEtaleGaloisCover.ofIsGalois A, a'.1, a'.2, ?_⟩
  have h := mapExactFunctor_eq_zero_of_fiberSheaf S c hS
    ((fiberSheaf S c).obj.map ((finiteEtaleToEtale X).map ι).op ν)
  rwa [hc] at h

end Stacks.EtaleCohomology

end
