module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.PointedGaloisCovering
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GeometricFibreDegree
public import Mathlib.CategoryTheory.Limits.Shapes.SingleObj

/-!
# The quotient of a Galois finite étale cover by a subgroup of its automorphisms

Let `X` be a connected scheme and `A` a Galois object of the Galois category `FÉt_X` of finite
étale covers of `X`, with automorphism group `G = Aut(A)`. For a subgroup `P ⊆ G` the quotient
`T = A/P` exists in `FÉt_X` (a Galois category has quotients by finite groups), and every fibre
functor carries it to the orbit set of `P` on the fibre of `A`. Hence:

* the projection `π : A ⟶ T` is surjective on every geometric fibre, and two points of a fibre of
  `A` have the same image exactly when they lie in one `P`-orbit;
* the degree of `T` over `X` is the index `[G : P]`, since `G` acts simply transitively on the
  fibres of `A` and `P` acts freely;
* if `X` is irreducible and geometrically unibranch, then `π : A ⟶ T` is a Galois covering of `T`
  with group `P` in the sense of `AlgebraicGeometry.EtaleGaloisCovering`.

## Main definitions

* `AlgebraicGeometry.galoisSubgroupQuotient`: the quotient `A/P` in `FÉt_X`.
* `AlgebraicGeometry.galoisSubgroupQuotientπ`: the projection `A ⟶ A/P`.
* `AlgebraicGeometry.galoisSubgroupQuotientCovering`: `A ⟶ A/P` as a Galois covering of `A/P`
  with group `P`.

## Main results

* `AlgebraicGeometry.exists_map_galoisSubgroupQuotientπ_eq`: a fibre point of `A/P` comes from `A`.
* `AlgebraicGeometry.exists_smul_eq_of_map_galoisSubgroupQuotientπ_eq`: two fibre points of `A`
  with the same image in `A/P` are in one `P`-orbit.
* `AlgebraicGeometry.isFiniteLocallyFreeOfRank_galoisSubgroupQuotient`: `A/P` has degree `[G : P]`.
* `AlgebraicGeometry.surjective_galoisSubgroupQuotientπ`: the projection `A ⟶ A/P` is surjective.

## References

* [Stacks Project, Tag 0GJ0](https://stacks.math.columbia.edu/tag/0GJ0)
* [Stacks Project, Tag 03SF](https://stacks.math.columbia.edu/tag/03SF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}} [ConnectedSpace X] (A : FiniteEtaleOver X) (P : Subgroup (Aut A))

/-- The action of a subgroup `P` of `Aut(A)` on `A`, as a diagram indexed by `P`. -/
def galoisSubgroupDiagram : SingleObj P ⥤ FiniteEtaleOver X :=
  SingleObj.functor ((Aut.toEnd (X := A)).comp P.subtype)

variable [Finite P]

/-- **The quotient `A/P`** of a finite étale cover by a finite group of automorphisms, in the
Galois category `FÉt_X`. -/
def galoisSubgroupQuotient : FiniteEtaleOver X :=
  colimit (galoisSubgroupDiagram A P)

/-- The projection `A ⟶ A/P`. -/
def galoisSubgroupQuotientπ : A ⟶ galoisSubgroupQuotient A P :=
  colimit.ι (galoisSubgroupDiagram A P) (SingleObj.star P)

/-- The projection `A ⟶ A/P` is invariant under `P`. -/
@[reassoc (attr := simp)]
theorem hom_comp_galoisSubgroupQuotientπ (p : P) :
    (p : Aut A).asIso.hom ≫ galoisSubgroupQuotientπ A P = galoisSubgroupQuotientπ A P :=
  colimit.w (galoisSubgroupDiagram A P) (p : SingleObj.star P ⟶ SingleObj.star P)

section Fiber

variable (x : GeometricPoint X)

/-- The orbit set of `P` on the geometric fibre of `A`, as a finite type. -/
abbrev galoisSubgroupOrbits : FintypeCat.{u} :=
  haveI : Fintype (MulAction.orbitRel.Quotient P ((finiteEtaleFiberFintypeFunctor X x).obj A)) :=
    Fintype.ofFinite _
  FintypeCat.of (MulAction.orbitRel.Quotient P ((finiteEtaleFiberFintypeFunctor X x).obj A))

/-- The cocone of the action diagram, followed by the fibre functor, on the orbit set. -/
def galoisSubgroupOrbitsCocone :
    Cocone (galoisSubgroupDiagram A P ⋙ finiteEtaleFiberFintypeFunctor X x) where
  pt := galoisSubgroupOrbits A P x
  ι :=
    { app := fun _ ↦ (FintypeCat.homMk
        (fun a : (finiteEtaleFiberFintypeFunctor X x).obj A ↦ (Quotient.mk'' a :
          MulAction.orbitRel.Quotient P ((finiteEtaleFiberFintypeFunctor X x).obj A))) :
            (finiteEtaleFiberFintypeFunctor X x).obj A ⟶ galoisSubgroupOrbits A P x)
      naturality := fun _ _ (p : P) ↦ by
        ext (a : (finiteEtaleFiberFintypeFunctor X x).obj A)
        exact (Quotient.sound ⟨p, rfl⟩ :
          (Quotient.mk'' ((p : Aut A) • a) :
            MulAction.orbitRel.Quotient P ((finiteEtaleFiberFintypeFunctor X x).obj A)) =
            Quotient.mk'' a) }

/-- The fibre functor preserves the quotient. -/
def isColimitGaloisSubgroupQuotient :
    IsColimit ((finiteEtaleFiberFintypeFunctor X x).mapCocone
      (colimit.cocone (galoisSubgroupDiagram A P))) :=
  isColimitOfPreserves (finiteEtaleFiberFintypeFunctor X x) (colimit.isColimit _)

/-- The map from the fibre of `A/P` to the orbit set. -/
def galoisSubgroupQuotientToOrbits :
    (finiteEtaleFiberFintypeFunctor X x).obj (galoisSubgroupQuotient A P) ⟶
      galoisSubgroupOrbits A P x :=
  (isColimitGaloisSubgroupQuotient A P x).desc (galoisSubgroupOrbitsCocone A P x)

/-- The map from the fibre of `A/P` to the orbit set sends the image of a fibre point of `A` to
its orbit. -/
theorem galoisSubgroupQuotientToOrbits_map (a : (finiteEtaleFiberFintypeFunctor X x).obj A) :
    galoisSubgroupQuotientToOrbits A P x
        ((finiteEtaleFiberFintypeFunctor X x).map (galoisSubgroupQuotientπ A P) a) =
      (Quotient.mk'' a : MulAction.orbitRel.Quotient P _) :=
  ConcreteCategory.congr_hom
    ((isColimitGaloisSubgroupQuotient A P x).fac (galoisSubgroupOrbitsCocone A P x)
      (SingleObj.star P)) a

/-- **Two fibre points of `A` with the same image in `A/P` lie in one `P`-orbit.** -/
theorem exists_smul_eq_of_map_galoisSubgroupQuotientπ_eq
    {a b : (finiteEtaleFiberFintypeFunctor X x).obj A}
    (h : (finiteEtaleFiberFintypeFunctor X x).map (galoisSubgroupQuotientπ A P) a =
      (finiteEtaleFiberFintypeFunctor X x).map (galoisSubgroupQuotientπ A P) b) :
    ∃ p : P, (finiteEtaleFiberFintypeFunctor X x).map (p : Aut A).asIso.hom a = b := by
  have h' := congrArg (galoisSubgroupQuotientToOrbits A P x) h
  rw [galoisSubgroupQuotientToOrbits_map, galoisSubgroupQuotientToOrbits_map] at h'
  exact Quotient.exact h'.symm

/-- The map from the orbit set back to the fibre of `A/P`, induced by the projection. -/
def galoisSubgroupOrbitsToQuotient :
    galoisSubgroupOrbits A P x ⟶
      (finiteEtaleFiberFintypeFunctor X x).obj (galoisSubgroupQuotient A P) :=
  FintypeCat.homMk (Quotient.lift
    (fun a ↦ (finiteEtaleFiberFintypeFunctor X x).map (galoisSubgroupQuotientπ A P) a)
    (fun a b hab ↦ by
      obtain ⟨p, rfl⟩ := hab
      change (finiteEtaleFiberFintypeFunctor X x).map (galoisSubgroupQuotientπ A P)
          ((finiteEtaleFiberFintypeFunctor X x).map (p : Aut A).asIso.hom b) = _
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, hom_comp_galoisSubgroupQuotientπ]))

/-- The map from the orbit set to the fibre of `A/P` sends the orbit of a fibre point of `A` to
its image. -/
theorem galoisSubgroupOrbitsToQuotient_mk (a : (finiteEtaleFiberFintypeFunctor X x).obj A) :
    galoisSubgroupOrbitsToQuotient A P x
        (Quotient.mk'' a : MulAction.orbitRel.Quotient P _) =
      (finiteEtaleFiberFintypeFunctor X x).map (galoisSubgroupQuotientπ A P) a :=
  rfl

/-- The map from the fibre of `A/P` to the orbit set, followed by the map back, is the
identity. -/
theorem galoisSubgroupQuotientToOrbits_comp_orbitsToQuotient :
    galoisSubgroupQuotientToOrbits A P x ≫ galoisSubgroupOrbitsToQuotient A P x = 𝟙 _ := by
  refine (isColimitGaloisSubgroupQuotient A P x).hom_ext fun j ↦ ?_
  ext (a : (finiteEtaleFiberFintypeFunctor X x).obj A)
  exact congrArg (galoisSubgroupOrbitsToQuotient A P x)
    (galoisSubgroupQuotientToOrbits_map A P x a)

/-- **Every fibre point of `A/P` comes from `A`.** -/
theorem exists_map_galoisSubgroupQuotientπ_eq
    (t : (finiteEtaleFiberFintypeFunctor X x).obj (galoisSubgroupQuotient A P)) :
    ∃ a, (finiteEtaleFiberFintypeFunctor X x).map (galoisSubgroupQuotientπ A P) a = t := by
  obtain ⟨a, ha⟩ := Quotient.exists_rep (galoisSubgroupQuotientToOrbits A P x t)
  exact ⟨a, (congrArg (galoisSubgroupOrbitsToQuotient A P x) ha).trans
    (ConcreteCategory.congr_hom (galoisSubgroupQuotientToOrbits_comp_orbitsToQuotient A P x) t)⟩

/-- The fibre of `A/P` is the orbit set of `P` on the fibre of `A`. -/
def galoisSubgroupQuotientFiberEquiv :
    (finiteEtaleFiberFintypeFunctor X x).obj (galoisSubgroupQuotient A P) ≃
      MulAction.orbitRel.Quotient P ((finiteEtaleFiberFintypeFunctor X x).obj A) where
  toFun := galoisSubgroupQuotientToOrbits A P x
  invFun := galoisSubgroupOrbitsToQuotient A P x
  left_inv t := ConcreteCategory.congr_hom
    (galoisSubgroupQuotientToOrbits_comp_orbitsToQuotient A P x) t
  right_inv q := by
    induction q using Quotient.inductionOn with
    | h a =>
      change galoisSubgroupQuotientToOrbits A P x
        ((finiteEtaleFiberFintypeFunctor X x).map (galoisSubgroupQuotientπ A P) a) = _
      rw [galoisSubgroupQuotientToOrbits_map]

end Fiber

/-- **Counting the orbits of a free action.** If every element other than `1` of a group `G`
acting on a finite set `α` fixes no point, then `|α| = |α/G| · |G|`. -/
theorem natCard_eq_natCard_orbitRel_mul_of_free {G α : Type*} [Group G] [MulAction G α]
    [Finite α] (hfree : ∀ (g : G) (a : α), g • a = a → g = 1) :
    Nat.card α = Nat.card (MulAction.orbitRel.Quotient G α) * Nat.card G := by
  classical
  have hinj : ∀ a : α, Function.Injective (fun g : G ↦ g • a) := fun a g h hgh ↦ by
    have hgh' : g • a = h • a := hgh
    have h1 : (h⁻¹ * g) • a = a := by
      rw [mul_smul, hgh', inv_smul_smul]
    exact (inv_mul_eq_one.mp (hfree _ a h1)).symm
  have horb : ∀ a : α, Nat.card (MulAction.orbit G a) = Nat.card G := fun a ↦
    Nat.card_range_of_injective (hinj a)
  have : Fintype (MulAction.orbitRel.Quotient G α) := Fintype.ofFinite _
  rw [Nat.card_congr (MulAction.selfEquivSigmaOrbits G α), Nat.card_sigma]
  simp only [horb, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]

variable [IsGalois A]

/-- **The geometric fibres of `A/P` have cardinality the index of `P`.** -/
theorem natCard_galoisSubgroupQuotient_fiber (x : GeometricPoint X) :
    Nat.card ((finiteEtaleFiberFintypeFunctor X x).obj (galoisSubgroupQuotient A P)) =
      P.index := by
  let Φ := finiteEtaleFiberFintypeFunctor X x
  obtain ⟨a₀⟩ := nonempty_fiber_of_isConnected Φ A
  have hAut : Nat.card (Φ.obj A) = Nat.card (Aut A) :=
    (Nat.card_congr (Equiv.ofBijective _ (evaluation_aut_bijective_of_isGalois Φ A a₀))).symm
  have hfree : ∀ (p : P) (a : Φ.obj A), p • a = a → p = 1 := fun p a hp ↦
    Subtype.ext <| evaluation_aut_injective_of_isConnected Φ A a <| by
      show Φ.map (p : Aut A).asIso.hom a = Φ.map (𝟙 A) a
      rwa [Φ.map_id]
  have hcount := natCard_eq_natCard_orbitRel_mul_of_free hfree
  rw [hAut, ← P.card_mul_index, mul_comm (Nat.card P)] at hcount
  rw [Nat.card_congr (galoisSubgroupQuotientFiberEquiv A P x)]
  exact (Nat.eq_of_mul_eq_mul_right Nat.card_pos hcount).symm

/-- **`A/P` is finite étale of degree `[Aut(A) : P]` over `X`.** -/
theorem isFiniteLocallyFreeOfRank_galoisSubgroupQuotient (x : GeometricPoint X) :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank (galoisSubgroupQuotient A P).hom P.index := by
  have h := isFiniteLocallyFreeOfRank_natCard_finiteEtaleFiber x (galoisSubgroupQuotient A P)
  rwa [show Nat.card ((finiteEtaleFiberFunctor x).obj (galoisSubgroupQuotient A P)) =
    P.index from natCard_galoisSubgroupQuotient_fiber A P x] at h

/-! ### The Galois covering `A ⟶ A/P` with group `P` -/

section Covering

/-- The projection `A ⟶ A/P` is étale. -/
instance etale_galoisSubgroupQuotientπ_left : Etale (galoisSubgroupQuotientπ A P).left :=
  MorphismProperty.of_postcomp @Etale (W' := @Etale) (galoisSubgroupQuotientπ A P).left
    (galoisSubgroupQuotient A P).hom (inferInstanceAs (Etale (galoisSubgroupQuotient A P).hom))
    ((MorphismProperty.Over.w (galoisSubgroupQuotientπ A P)).symm ▸
      inferInstanceAs (Etale A.hom))

omit [IsGalois A] in
/-- **The projection `A ⟶ A/P` is surjective.** -/
theorem surjective_galoisSubgroupQuotientπ :
    Function.Surjective (galoisSubgroupQuotientπ A P).left.base := by
  intro t
  let T := galoisSubgroupQuotient A P
  let x' := (T.left.algClosedPoint t).map T.hom
  let tb : (finiteEtaleFiberFintypeFunctor X x').obj T :=
    (⟨(T.left.algClosedPoint t).hom, rfl⟩ : finiteEtaleFiber x' T)
  obtain ⟨a, ha⟩ := exists_map_galoisSubgroupQuotientπ_eq A P x' tb
  have ha' : a.1 ≫ (galoisSubgroupQuotientπ A P).left = (T.left.algClosedPoint t).hom :=
    congrArg Subtype.val ha
  refine ⟨a.1.base default, ?_⟩
  rw [← Scheme.Hom.comp_apply, ha']
  exact Scheme.algClosedPointHom_apply T.left t default

variable [IrreducibleSpace X] (hX : IsGeometricallyUnibranch X)

include hX in
/-- The underlying scheme of a Galois cover of an irreducible, geometrically unibranch scheme is
irreducible. -/
theorem irreducibleSpace_left_of_isGalois : IrreducibleSpace A.left :=
  have : ConnectedSpace A.left := connectedSpace_left_of_isConnected A inferInstance
  have : IrreducibleSpace ((Functor.fromPUnit X).obj A.right) :=
    inferInstanceAs (IrreducibleSpace X)
  irreducibleSpace_of_etale_of_isGeometricallyUnibranch (X := X) A.hom hX

omit [IsGalois A] [IrreducibleSpace X] in
/-- **Two morphisms into `A` with the same composite to `A/P` differ by an element of `P` near
every point.** -/
theorem exists_mem_agreeLocus_galoisSubgroupQuotientπ {W : Scheme.{u}} (a b : W ⟶ A.left)
    (hab : a ≫ (galoisSubgroupQuotientπ A P).left = b ≫ (galoisSubgroupQuotientπ A P).left)
    (w : W) :
    ∃ (p : P) (hw : (a ≫ (p : Aut A).asIso.hom.left) ≫ (galoisSubgroupQuotientπ A P).left =
        b ≫ (galoisSubgroupQuotientπ A P).left),
      w ∈ Scheme.Hom.agreeLocus (galoisSubgroupQuotientπ A P).left _ _ hw := by
  have hw₀ : (galoisSubgroupQuotientπ A P).left ≫ (galoisSubgroupQuotient A P).hom = A.hom :=
    MorphismProperty.Over.w (galoisSubgroupQuotientπ A P)
  have hab' : a ≫ A.hom = b ≫ A.hom := by
    rw [← hw₀, ← Category.assoc, ← Category.assoc, hab]
  let x' := (W.algClosedPoint w).map (a ≫ A.hom)
  let F := finiteEtaleFiberFintypeFunctor X x'
  let ea : F.obj A := fiberPointOfComp w a
  let eb : F.obj A := (⟨(W.algClosedPoint w).hom ≫ b, by
      rw [Category.assoc, ← hab']; rfl⟩ : finiteEtaleFiber x' A)
  have hπ : F.map (galoisSubgroupQuotientπ A P) ea = F.map (galoisSubgroupQuotientπ A P) eb := by
    apply Subtype.ext
    show ((W.algClosedPoint w).hom ≫ a) ≫ (galoisSubgroupQuotientπ A P).left =
      ((W.algClosedPoint w).hom ≫ b) ≫ (galoisSubgroupQuotientπ A P).left
    rw [Category.assoc, Category.assoc, hab]
  obtain ⟨p, hp⟩ := exists_smul_eq_of_map_galoisSubgroupQuotientπ_eq A P x' hπ
  have hp' : (W.algClosedPoint w).hom ≫ a ≫ (p : Aut A).asIso.hom.left =
      (W.algClosedPoint w).hom ≫ b := by
    rw [← finiteEtaleFiberFintypeFunctor_map_fiberPointOfComp]
    exact congrArg Subtype.val hp
  have hw : (a ≫ (p : Aut A).asIso.hom.left) ≫ (galoisSubgroupQuotientπ A P).left =
      b ≫ (galoisSubgroupQuotientπ A P).left := by
    rw [Category.assoc]
    show a ≫ ((p : Aut A).asIso.hom ≫ galoisSubgroupQuotientπ A P).left = _
    rw [hom_comp_galoisSubgroupQuotientπ]
    exact hab
  refine ⟨p, hw, ?_⟩
  rw [← Scheme.algClosedPointHom_apply W w default]
  exact Scheme.Hom.mem_agreeLocus_of_comp_eq _ _ _ hw _ hp' _

/-- **`A ⟶ A/P` is a Galois covering of `A/P` with group `P`**, for `X` irreducible and
geometrically unibranch. -/
def galoisSubgroupQuotientCovering : EtaleGaloisCovering (galoisSubgroupQuotient A P).left P where
  cover := Scheme.Etale.mk (galoisSubgroupQuotientπ A P).left
  act p := (p : Aut A).asIso.hom.left
  act_comp_hom p :=
    congrArg (fun f ↦ f.left) (hom_comp_galoisSubgroupQuotientπ A P p)
  act_one := rfl
  act_mul _ _ := rfl
  surjective := surjective_galoisSubgroupQuotientπ A P
  irreducibleSpace := irreducibleSpace_left_of_isGalois A hX
  exists_mem_agreeLocus a b hab w :=
    exists_mem_agreeLocus_galoisSubgroupQuotientπ A P a b hab w
  eq_of_comp_eq c _ _ hc := Subtype.ext (aut_eq_of_comp_eq c hc)

end Covering

end AlgebraicGeometry

end
