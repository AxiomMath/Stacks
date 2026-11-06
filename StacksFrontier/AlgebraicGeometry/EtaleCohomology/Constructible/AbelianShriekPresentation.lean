module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Etale.FiniteSupportStalkVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.AbelianShriekConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ColimitOfConstructibles
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ConstructibleCoequalizerPresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.GlobalStratification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.IntegerShriekPresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointDomination
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.Coefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkIsomorphismCriterion
public import StacksCore.Tactic.StacksAttribute
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ConstructibleCoequalizerPresentation

/-!
# Constructible abelian sheaves are exactly the finite cokernels of `Z/nZ` extensions by zero

Let `X` be a quasi-compact and quasi-separated scheme. An abelian sheaf on the small étale site
of `X` is constructible exactly when it is a cokernel

`Coker(⨁_{j = 1, …, m} j_{V_j!}(Z/m_jZ) ⟶ ⨁_{i = 1, …, n} j_{U_i!}(Z/n_iZ))`

with the `V_j` and `U_i` objects of `X_étale` and the `m_j`, `n_i` positive integers, and the
`V_j` and `U_i` may be taken quasi-compact and quasi-separated or, what is a stronger statement
in this direction, affine. This is Stacks 09YT.

One inclusion is `Constructible/ColimitOfConstructibles.lean`: such a cokernel is constructible
because constructibility is a weak Serre condition and the summands `j_{U!}(Z/nZ)` are
constructible by Stacks 03S8 (2), which this library proves in
`Constructible/AbelianShriekConstructible.lean` as
`AlgebraicGeometry.abelianShriekZModIsConstructible`. That file cannot discharge the input where
the cokernel statement is made, because it is above `Constructible/ColimitOfConstructibles.lean`
in the import order; the two meet here.

The other inclusion is the content of this file and is the source's argument, "apply Stacks 095N
with `Λ = Z/nZ` and the fact that a constructible abelian sheaf on a quasi-compact `X` is
annihilated by some positive integer". It is carried out in three steps.

*The annihilation.* A constructible abelian sheaf `F` on a quasi-compact quasi-separated `X` is
annihilated by a single positive integer: `N • 𝟙 F = 0`. On each of the finitely many strata of a
global constructible stratification the inverse image of `F` is finite locally constant; a finite
locally constant abelian sheaf on a site whose terminal object is quasi-compact is annihilated by
the product of the cardinalities of the finitely many constant values of a trivialising covering,
and a stratum of a constructible stratification of a quasi-compact quasi-separated scheme is
quasi-compact. The resulting integers are multiplied together, and the product annihilates `F`
itself because it annihilates every geometric stalk: the image of a geometric point lies in some
stratum, and the stalk there is the stalk of the inverse image to that stratum.

*The integral presentation.* Abelian sheaves are sheaves of `ℤ`-modules, and the forward half of
Stacks 095N at `ℤ` — `AlgebraicGeometry.hasFiniteShriekPresentation_int_of_uliftInt` composed
with the affine form of the library's Stacks 095N — presents `F` as a cokernel of a map between
finite direct sums of extensions by zero of the *constant* sheaf `ℤ` at affine étale objects.
This avoids the comparison between abelian sheaves annihilated by `n` and sheaves of
`Z/nZ`-modules, which is not available: `CategoryTheory.Sheaf.coefficientEquivalence` needs an
equivalence of coefficient categories, and `AddCommGrpCat` is not equivalent to
`ModuleCat (ZMod n)`.

*The reduction mod `N`.* Quotienting the integral presentation by `N` turns it into a
presentation by `Z/NZ`: if `F` is the cokernel of `f : A ⟶ B` and is annihilated by `N`, then it
is also the cokernel of the induced map `A/N ⟶ B/N`, and `A/N`, `B/N` are the corresponding
direct sums of the sheaves `j_{U!}(Z/NZ)` because extension by zero of a constant sheaf is an
additive functor of the constant value and `ULift ℤ / N ≅ ULift (Z/NZ)`.

## Main definitions

* `AlgebraicGeometry.abelianShriekConstant` — the abelian sheaf `j_{U!}\underline{M}_U`, the
  extension by zero along the étale object `U` of the constant sheaf with value `M`. The sheaves
  `AlgebraicGeometry.abelianShriekZMod` are its values at `M = Z/nZ`.

## Main results

* `AlgebraicGeometry.exists_nsmul_id_eq_zero_of_isConstructibleAbelianSheaf` — **a constructible
  abelian sheaf on a quasi-compact quasi-separated scheme is annihilated by a positive integer.**
  This is the input the source leaves to the reader and whose absence
  `StacksFrontier/AlgebraicGeometry/EtaleCohomology/ProperBaseChange/PrimaryDevissage.lean` records.
* `AlgebraicGeometry.isConstructibleAbelianSheaf_iff_hasFiniteZModShriekPresentation` and
  `AlgebraicGeometry.isConstructibleAbelianSheaf_iff_affineZModShriekPresentation` —
  **Stacks 09YT**, at quasi-compact quasi-separated and at affine étale objects.

## Implementation notes

The coefficient universe is `AddCommGrpCat.{u + 1}`, as in the rest of the constructibility
development, `u` being the universe of the schemes.

The annihilation is proved as `N • 𝟙 F = 0`, a statement about the identity morphism, rather than
pointwise on sections: that is the form in which the cokernel construction of the third step
consumes it, and the two are equivalent for a sheaf of abelian groups.

## References

* [Stacks Project, Tag 09YT](https://stacks.math.columbia.edu/tag/09YT)
* [Stacks Project, Tag 095N](https://stacks.math.columbia.edu/tag/095N)
* [Stacks Project, Tag 03S8](https://stacks.math.columbia.edu/tag/03S8)
* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance 2000] Sheaf.instHasColimitsOfShape Sheaf.instHasFiniteCoproducts

universe w v u

namespace AddCommGrpCat

/-- A positive multiple of the identity of a finite abelian group vanishes: the cardinality
annihilates every element. -/
public theorem natCard_nsmul_id_eq_zero (A : AddCommGrpCat.{w}) [Finite A] :
    Nat.card A • (𝟙 A) = 0 := by
  ext x
  classical
  let : Fintype A := Fintype.ofFinite A
  have hpow : (Multiplicative.ofAdd x : Multiplicative A) ^ Nat.card A = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (orderOf_dvd_natCard (Multiplicative.ofAdd x))
  exact congrArg Multiplicative.toAdd hpow

/-- An isomorphism transports annihilation by `n` of every element. -/
public theorem nsmul_eq_zero_of_iso {A D : AddCommGrpCat.{w}} (e : A ≅ D) (n : ℕ)
    (h : ∀ x : A, n • x = 0) (y : D) : n • y = 0 := by
  have hy : e.hom (e.inv y) = y := by
    rw [← CategoryTheory.comp_apply, e.inv_hom_id]
    rfl
  rw [← hy, ← _root_.map_nsmul, h, map_zero]

/-- `N` annihilates `Z/NZ`. -/
public theorem nsmul_id_uliftZMod_eq_zero (N : ℕ) :
    N • (𝟙 (AddCommGrpCat.of (ULift.{w} (ZMod N)))) = 0 := by
  ext y
  show N • y.down = (0 : ZMod N)
  rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]

/-- Reduction of `ULift ℤ` modulo `N`, as a morphism of abelian groups. -/
public def uliftIntToZMod (N : ℕ) :
    AddCommGrpCat.of (ULift.{w} ℤ) ⟶ AddCommGrpCat.of (ULift.{w} (ZMod N)) :=
  ofHom (((AddEquiv.ulift (α := ZMod N)).symm.toAddMonoidHom).comp
    ((Int.castAddHom (ZMod N)).comp (AddEquiv.ulift (α := ℤ)).toAddMonoidHom))

/-- Reduction modulo `N` is an epimorphism `ULift ℤ ⟶ ULift (ZMod N)`. -/
public instance epi_uliftIntToZMod (N : ℕ) : Epi (uliftIntToZMod.{w} N) := by
  rw [AddCommGrpCat.epi_iff_surjective]
  intro y
  obtain ⟨z, hz⟩ := ZMod.intCast_surjective y.down
  exact ⟨ULift.up z, ULift.ext hz⟩

/-- Multiplication by `N` on `ULift ℤ`, followed by reduction modulo `N`, is zero. -/
public theorem nsmul_id_comp_uliftIntToZMod (N : ℕ) :
    (N • 𝟙 (AddCommGrpCat.of (ULift.{w} ℤ))) ≫ uliftIntToZMod.{w} N = 0 := by
  rw [Preadditive.nsmul_comp, Category.id_comp,
    show (N • uliftIntToZMod.{w} N) = uliftIntToZMod.{w} N ≫
      (N • 𝟙 (AddCommGrpCat.of (ULift.{w} (ZMod N)))) by
        rw [Preadditive.comp_nsmul, Category.comp_id],
    nsmul_id_uliftZMod_eq_zero, comp_zero]

/-- **`ULift ℤ` modulo `N` is `ULift (Z/NZ)`.** Reduction modulo `N` is a cokernel of
multiplication by `N`: it kills `N`, it is surjective, and a morphism out of `ULift ℤ` killing `N`
factors through `Z/NZ` by `ZMod.lift`. -/
public def cokernelNsmulUliftIntIso (N : ℕ) :
    cokernel (N • 𝟙 (AddCommGrpCat.of (ULift.{w} ℤ))) ≅
      AddCommGrpCat.of (ULift.{w} (ZMod N)) :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
    (CokernelCofork.IsColimit.ofπ' (uliftIntToZMod.{w} N)
      (nsmul_id_comp_uliftIntToZMod.{w} N) (fun {A} k w => by
        rw [Preadditive.nsmul_comp, Category.id_comp] at w
        have hz : N • k.hom (ULift.up (1 : ℤ)) = 0 := by
          simpa using ConcreteCategory.congr_hom w (ULift.up (1 : ℤ))
        have hup : (ULift.up ((N : ℕ) : ℤ) : ULift.{w} ℤ) = N • (ULift.up (1 : ℤ)) := by
          refine ULift.ext ?_
          show ((N : ℕ) : ℤ) = N • (1 : ℤ)
          simp
        have hf : (k.hom.comp (AddEquiv.ulift (α := ℤ)).symm.toAddMonoidHom)
            ((N : ℕ) : ℤ) = 0 := by
          show k.hom (ULift.up ((N : ℕ) : ℤ)) = 0
          rw [hup, _root_.map_nsmul, hz]
        refine ⟨ofHom ((ZMod.lift N
          ⟨k.hom.comp (AddEquiv.ulift (α := ℤ)).symm.toAddMonoidHom, hf⟩).comp
            (AddEquiv.ulift (α := ZMod N)).toAddMonoidHom), ?_⟩
        ext x
        show ZMod.lift N ⟨k.hom.comp (AddEquiv.ulift (α := ℤ)).symm.toAddMonoidHom, hf⟩
          ((x.down : ZMod N)) = k.hom x
        rw [ZMod.lift_coe]
        rfl))

end AddCommGrpCat

namespace CategoryTheory

/-- An isomorphism transports the vanishing of a multiple of the identity. -/
public theorem nsmul_id_eq_zero_of_iso {C : Type u} [Category.{v} C] [Preadditive C] {A D : C}
    (e : A ≅ D) (n : ℕ) (h : n • (𝟙 A) = 0) : n • (𝟙 D) = 0 := by
  apply (cancel_epi e.hom).1
  simpa only [Preadditive.nsmul_comp, Preadditive.comp_nsmul, Category.id_comp, Category.comp_id,
    zero_comp, comp_zero] using congrArg (fun t => t ≫ e.hom) h

namespace Limits

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCokernels C]

/-- The cokernel of `n • 𝟙 A` is annihilated by `n`. -/
public theorem nsmul_id_cokernel_nsmul_id_eq_zero (A : C) (n : ℕ) :
    n • (𝟙 (cokernel (n • (𝟙 A)))) = 0 := by
  apply (cancel_epi (cokernel.π (n • (𝟙 A)))).1
  simpa only [Preadditive.nsmul_comp, Preadditive.comp_nsmul, Category.id_comp, Category.comp_id,
    comp_zero] using cokernel.condition (n • (𝟙 A))

/-- **An object annihilated by `n` which is a cokernel is a cokernel of the induced map between
the quotients by `n`.** If `F` is the cokernel of `f : A ⟶ B` and `n • 𝟙 F = 0`, then `F` is also
the cokernel of the map `A/n ⟶ B/n` induced by `f`. This is the step by which an integral
presentation of a sheaf annihilated by `n` becomes a presentation by `Z/nZ`. -/
public theorem exists_cokernel_nsmul_of_nsmul_id_eq_zero {A B F : C} (f : A ⟶ B)
    (e : cokernel f ≅ F) (n : ℕ) (hn : n • (𝟙 F) = 0) :
    ∃ g : cokernel (n • (𝟙 A)) ⟶ cokernel (n • (𝟙 B)), Nonempty (cokernel g ≅ F) := by
  let g := cokernel.map (n • (𝟙 A)) (n • (𝟙 B)) f f (by
    simp only [Preadditive.nsmul_comp, Preadditive.comp_nsmul, Category.id_comp, Category.comp_id])
  let q : cokernel (n • (𝟙 B)) ⟶ cokernel f :=
    cokernel.desc _ (cokernel.π f) (by
      calc
        (n • 𝟙 B) ≫ cokernel.π f = cokernel.π f ≫ (n • 𝟙 (cokernel f)) := by
          simp only [Preadditive.nsmul_comp, Preadditive.comp_nsmul, Category.id_comp,
            Category.comp_id]
        _ = 0 := by rw [nsmul_id_eq_zero_of_iso e.symm n hn, comp_zero])
  have hgq : g ≫ q = 0 := by
    apply (cancel_epi (cokernel.π (n • (𝟙 A)))).1
    simp [g, q]
  let h : cokernel g ⟶ cokernel f := cokernel.desc g q hgq
  have hfq : f ≫ cokernel.π (n • (𝟙 B)) ≫ cokernel.π g = 0 := by
    calc
      _ = (cokernel.π (n • (𝟙 A)) ≫ g) ≫ cokernel.π g := by
        dsimp [g]
        rw [cokernel.π_desc, Category.assoc]
      _ = 0 := by rw [Category.assoc, cokernel.condition, comp_zero]
  let k : cokernel f ⟶ cokernel g :=
    cokernel.desc f (cokernel.π (n • (𝟙 B)) ≫ cokernel.π g) hfq
  refine ⟨g, ⟨?_ ≪≫ e⟩⟩
  refine ⟨h, k, ?_, ?_⟩
  · apply (cancel_epi (cokernel.π g)).1
    apply (cancel_epi (cokernel.π (n • (𝟙 B)))).1
    simp [h, k, q]
  · apply (cancel_epi (cokernel.π f)).1
    simp [h, k, q]

/-- Quotienting a coproduct by `n` is the coproduct of the quotients by `n`. -/
public def cokernelNsmulCoproductIso {I : Type*} [HasColimitsOfShape (Discrete I) C] (A : I → C)
    (n : ℕ) : cokernel (n • (𝟙 (∐ A))) ≅ ∐ fun i => cokernel (n • (𝟙 (A i))) := by
  let D := Discrete.functor A
  let t := n • (𝟙 D)
  let L : (Discrete I ⥤ C) ⥤ C := colim
  letI : L.Additive := by
    constructor
    intro F G p q
    apply colimit.hom_ext
    intro j
    simp [L, Preadditive.comp_add, Preadditive.add_comp]
  letI : HasCokernel t := hasCokernel_of_hasCokernel_app t
  have ht : L.map t = n • (𝟙 (∐ A)) := by
    change L.map (n • (𝟙 D)) = _
    rw [Functor.map_nsmul, L.map_id]
    rfl
  refine (cokernelIsoOfEq ht).symm ≪≫ (PreservesCokernel.iso L t).symm ≪≫ ?_
  letI (i : Discrete I) := evaluation_preservesColimit_of_hasCokernel_app t i
  exact HasColimit.isoOfNatIso (Discrete.natIso fun i =>
    (PreservesCokernel.iso ((evaluation (Discrete I) C).obj i) t) ≪≫ cokernelIsoOfEq rfl)

end Limits

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- A multiple of the identity of a sheaf of abelian groups vanishes as soon as it vanishes after
restriction to the members of one covering family of a terminal object: every section over every
object restricts, along a covering sieve, to sections over objects lying over the members of that
family. -/
public theorem nsmul_id_eq_zero_of_cover (F : Sheaf J AddCommGrpCat.{w}) (T : C)
    (hT : IsTerminal T) {I : Type*} (V : I → C) (f : ∀ i, V i ⟶ T)
    (hf : Sieve.ofArrows V f ∈ J T) (n : ℕ)
    (hn : ∀ i, n • (𝟙 (F.over (V i))) = 0) : n • (𝟙 F) = 0 := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply F.property.hom_ext ⟨_, J.pullback_stable (hT.from U.unop) hf⟩
  intro a
  obtain ⟨i, g, hg⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp a.hf
  have h := congrArg
    (fun t : F.over (V i) ⟶ F.over (V i) => t.hom.app (Opposite.op (Over.mk g))) (hn i)
  change n • (𝟙 (F.obj.obj (Opposite.op a.Y))) = 0 at h
  show (n • 𝟙 (F.obj.obj U)) ≫ F.obj.map a.f.op = 0 ≫ F.obj.map a.f.op
  simpa only [Preadditive.comp_nsmul, Preadditive.nsmul_comp, Category.id_comp, Category.comp_id,
    comp_zero, zero_comp] using congrArg (fun t => F.obj.map a.f.op ≫ t) h

/-- Annihilation of a restricted sheaf passes to a smaller object and to a multiple of the
annihilator. -/
public theorem nsmul_id_over_eq_zero_of_dvd (F : Sheaf J AddCommGrpCat.{w}) {U V : C} (f : U ⟶ V)
    {n m : ℕ} (hn : n • (𝟙 (F.over V)) = 0) (hnm : n ∣ m) : m • (𝟙 (F.over U)) = 0 := by
  obtain ⟨k, rfl⟩ := hnm
  have h : n • (𝟙 (F.over U)) = 0 := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext W
    exact congrArg
      (fun t : F.over V ⟶ F.over V => t.hom.app (Opposite.op (Over.mk (W.unop.hom ≫ f)))) hn
  rw [mul_nsmul, h, smul_zero]

end CategoryTheory

namespace Stacks.ConstantSheaf

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]

/-- Every object of the site has a covering on each member of which the restriction of a finite
locally constant abelian sheaf is annihilated by a positive integer: the integer is the
cardinality of the constant value there. -/
public theorem exists_cover_nsmul_id_eq_zero (F : Sheaf J AddCommGrpCat.{w})
    (hF : IsFiniteLocallyConstant J F) (U : C) :
    ∃ (I : Type (max u v)) (V : I → C) (f : ∀ i, V i ⟶ U),
      Sieve.ofArrows V f ∈ J U ∧
      ∃ N : I → ℕ, ∀ i, 0 < N i ∧ N i • (𝟙 (F.over (V i))) = 0 := by
  classical
  obtain ⟨I, V, f, hf, hV⟩ := hF.exists_finite_cover U
  choose E hE e using hV
  refine ⟨I, V, f, hf, fun i => Nat.card (E i), fun i => ?_⟩
  have : Finite (E i) := hE i
  obtain ⟨e⟩ := e i
  let H := constantSheaf (J.over (V i)) AddCommGrpCat.{w}
  let : H.Additive := by
    let := preservesBinaryBiproducts_of_preservesBinaryCoproducts H
    exact Functor.additive_of_preservesBinaryBiproducts H
  have hconst : Nat.card (E i) • (𝟙 (H.obj (E i))) = 0 := by
    simpa only [Functor.map_nsmul, H.map_id, Functor.map_zero] using
      congrArg H.map (AddCommGrpCat.natCard_nsmul_id_eq_zero (E i))
  exact ⟨Nat.card_pos, CategoryTheory.nsmul_id_eq_zero_of_iso e _ hconst⟩

/-- **A finite locally constant abelian sheaf on a site with a quasi-compact terminal object is
annihilated by a positive integer.** A trivialising covering of the terminal object is refined by
a finite family, and the product of the cardinalities of the constant values along that family
annihilates the sheaf. -/
public theorem exists_nsmul_id_eq_zero_of_isFiniteLocallyConstant (F : Sheaf J AddCommGrpCat.{w})
    (hF : IsFiniteLocallyConstant J F) (T : C) (hT : IsTerminal T)
    (hc : J.IsQuasiCompactObject T) : ∃ n : ℕ, 0 < n ∧ n • (𝟙 F) = 0 := by
  classical
  obtain ⟨I, V, f, hf, N, hN⟩ := exists_cover_nsmul_id_eq_zero J F hF T
  let E : PreZeroHypercover T := ⟨I, V, f⟩
  obtain ⟨D, φ, hD, hφ⟩ := hc E hf
  let S := hφ.toFinset
  refine ⟨∏ i ∈ S, N i, Finset.prod_pos fun i _ => (hN i).1, ?_⟩
  refine CategoryTheory.nsmul_id_eq_zero_of_cover J F T hT D.X D.f hD _ fun i => ?_
  exact CategoryTheory.nsmul_id_over_eq_zero_of_dvd J F (φ.h₀ i) (hN (φ.s₀ i)).2
    (Finset.dvd_prod_of_mem N (by simp [S]))

end Stacks.ConstantSheaf

namespace AlgebraicGeometry.SmallEtale

/-- A multiple of the identity which vanishes on an abelian étale sheaf annihilates every element
of every stalk: an element of a stalk is the germ of a section, and the section is annihilated. -/
public theorem nsmul_etaleStalk_eq_zero_of_nsmul_id_eq_zero (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (t : GeometricPoint S) [UnivLE.{u, v}]
    (G : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v})
    [HasColimit (etaleStalkDiagram B S hS t G.obj)] (n : ℕ) (h : n • (𝟙 G) = 0)
    (g : ↑(etaleStalk B S hS t G.obj)) : n • g = 0 := by
  obtain ⟨W, q, a, rfl⟩ := exists_etaleGerm_eq B S hS t G.obj g
  rw [← etaleGerm_nsmul_of_hasColimit B S hS t G.obj W q n a]
  have h' := congrArg (fun φ : G ⟶ G => φ.hom.app (op W)) h
  change n • (𝟙 (G.obj.obj (op W))) = 0 at h'
  have ha : n • a = 0 := by simpa using ConcreteCategory.congr_hom h' a
  rw [ha]
  exact etaleGerm_zero B S hS t G.obj W q

end AlgebraicGeometry.SmallEtale

namespace AlgebraicGeometry

open Stacks.ConstantSheaf

variable (B : BigEtaleSite.{u}) (X : B.Scheme)

/-- The abelian sheaf `j_{U!}\underline{M}_U` on the small étale site of `X`: the extension by
zero along the étale object `U` of the constant sheaf with value `M`. The sheaves
`AlgebraicGeometry.abelianShriekZMod` displayed by Stacks 09YT are its values at `M = Z/nZ`. -/
public def abelianShriekConstant (M : AddCommGrpCat.{u + 1})
    (U : SmallEtale B X.obj X.property) :
    Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1} :=
  (abelianExtensionByZero B X.obj X.property U).obj
    ((constantSheaf (SmallEtale.topology B U.obj.left.obj U.obj.left.property)
      AddCommGrpCat.{u + 1}).obj M)

/-- `j_{U!}(Z/nZ)` is `j_{U!}\underline{M}` at `M = Z/nZ`. -/
public theorem abelianShriekZMod_eq_abelianShriekConstant (n : ℕ)
    (U : SmallEtale B X.obj X.property) :
    abelianShriekZMod B X n U =
      abelianShriekConstant B X (AddCommGrpCat.of (ULift.{u + 1} (ZMod n))) U :=
  rfl

/-- Quotienting `j_{U!}\underline{M}` by `n` quotients the constant value: extension by zero of a
constant sheaf is an additive functor of that value, so it preserves the cokernel of `n • 𝟙`. -/
public def cokernelNsmulAbelianShriekConstantIso (M : AddCommGrpCat.{u + 1})
    (U : SmallEtale B X.obj X.property) (n : ℕ) :
    cokernel (n • (𝟙 (abelianShriekConstant B X M U))) ≅
      abelianShriekConstant B X (cokernel (n • (𝟙 M))) U := by
  let H := constantSheaf (SmallEtale.topology B U.obj.left.obj U.obj.left.property)
      AddCommGrpCat.{u + 1} ⋙ abelianExtensionByZero B X.obj X.property U
  letI : H.Additive := by
    letI := preservesBinaryBiproducts_of_preservesBinaryCoproducts H
    exact Functor.additive_of_preservesBinaryBiproducts H
  exact (cokernelIsoOfEq (show H.map (n • (𝟙 M)) = n • (𝟙 (H.obj M)) by
    rw [Functor.map_nsmul, H.map_id])).symm ≪≫ (PreservesCokernel.iso H _).symm

/-- Quotienting `j_{U!}\underline{ULift ℤ}` by `N` gives `j_{U!}(Z/NZ)`. -/
public def cokernelNsmulAbelianShriekZModIso (U : SmallEtale B X.obj X.property) (N : ℕ) :
    cokernel (N • (𝟙 (abelianShriekConstant B X (AddCommGrpCat.of (ULift.{u + 1} ℤ)) U))) ≅
      abelianShriekZMod B X N U :=
  cokernelNsmulAbelianShriekConstantIso B X (AddCommGrpCat.of (ULift.{u + 1} ℤ)) U N ≪≫
    (abelianExtensionByZero B X.obj X.property U).mapIso
      ((constantSheaf (SmallEtale.topology B U.obj.left.obj U.obj.left.property)
        AddCommGrpCat.{u + 1}).mapIso (AddCommGrpCat.cokernelNsmulUliftIntIso.{u + 1} N))

variable
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) AddCommGrpCat.{u + 1}]

/-- **A finite locally constant abelian sheaf on the small étale site of a quasi-compact scheme is
annihilated by a positive integer.** The final object of the site is the scheme itself, which is
a quasi-compact object of the site. -/
public theorem exists_nsmul_id_eq_zero_of_isFiniteLocallyConstant_smallEtale
    (hXc : CompactSpace X.obj)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hF : IsFiniteLocallyConstant (SmallEtale.topology B X.obj X.property) F) :
    ∃ n : ℕ, 0 < n ∧ n • (𝟙 F) = 0 :=
  exists_nsmul_id_eq_zero_of_isFiniteLocallyConstant _ F hF
    (SmallEtale.final B X.obj X.property) (SmallEtale.finalIsTerminal B X.obj X.property)
    (SmallEtale.isQuasiCompactObject_of_compactSpace B X.obj X.property _ hXc)

/-- **A multiple of the identity of an abelian étale sheaf vanishes as soon as it annihilates
every geometric stalk.** A section over an étale object is zero once its germ vanishes at a
geometric point above every point of that object, by Stacks 04FR. -/
public theorem nsmul_id_eq_zero_of_forall_etaleStalk
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) (n : ℕ)
    (h : ∀ (t : GeometricPoint X.obj) (g : ↑(etaleStalk B X.obj X.property t F.obj)),
      n • g = 0) :
    n • (𝟙 F) = 0 := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext W
  ext σ
  show n • σ = 0
  have hsubset : Set.range ((SmallEtale.toScheme B X.obj X.property).map (𝟙 W.unop)).base ⊆
      (SmallEtale.zeroOpen B X.obj X.property F W.unop (n • σ) :
        Set ((SmallEtale.toScheme B X.obj X.property).obj W.unop)) := by
    intro x _
    have hz : SmallEtale.etaleGerm B X.obj X.property
        (geometricPointOfEtalePoint B X.obj X.property W.unop x) F.obj W.unop
        (geometricPointOfEtalePointLift B X.obj X.property W.unop x) (n • σ) = 0 := by
      rw [SmallEtale.etaleGerm_nsmul_of_hasColimit]
      exact h _ _
    have hmem := (SmallEtale.etaleGerm_eq_zero_iff_mem_zeroOpen B X.obj X.property
      (geometricPointOfEtalePoint B X.obj X.property W.unop x) F W.unop
      (geometricPointOfEtalePointLift B X.obj X.property W.unop x) (n • σ)).1 hz
    rwa [geometricPointOfEtalePointLift_base B X.obj X.property W.unop x] at hmem
  simpa using (SmallEtale.map_eq_zero_iff_range_subset_zeroOpen B X.obj X.property F W.unop
    (n • σ) W.unop (𝟙 _)).mpr hsubset

/-- **A constructible abelian étale sheaf on a quasi-compact quasi-separated scheme is annihilated
by a positive integer.** This is the input the source of Stacks 09YT leaves to the reader.

A global constructible stratification of `X` has finitely many strata, each quasi-compact, on each
of which the inverse image of the sheaf is finite locally constant and so annihilated by some
positive integer; the product of those integers annihilates every geometric stalk of the sheaf,
because the image of a geometric point of `X` lies in some stratum and the stalk there is the
stalk of the inverse image to that stratum. -/
public theorem exists_nsmul_id_eq_zero_of_isConstructibleAbelianSheaf
    (hXc : CompactSpace X.obj) (hXq : QuasiSeparatedSpace X.obj)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hF : IsConstructibleAbelianSheaf B X F) : ∃ N : ℕ, 0 < N ∧ N • (𝟙 F) = 0 := by
  classical
  obtain ⟨s, hs⟩ := (isConstructibleFiniteSheaf_iff_exists_stratification B X F).mp hF
  have he (i : Fin s.n) : ∃ n : ℕ, 0 < n ∧ n • (𝟙
      (((smallEtaleBaseChange B (s.inclusion i)).sheafPullback AddCommGrpCat.{u + 1}
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B (s.piece i).obj (s.piece i).property)).obj F)) = 0 :=
    exists_nsmul_id_eq_zero_of_isFiniteLocallyConstant_smallEtale B (s.piece i)
      (compactSpace_constructibleStratification_piece B X s i) _ (hs i)
  choose n hn hann using he
  refine ⟨∏ i, n i, Finset.prod_pos fun i _ => hn i, ?_⟩
  refine nsmul_id_eq_zero_of_forall_etaleStalk B X F _ fun t g => ?_
  have hx : t.hom default ∈ ⋃ i, Set.range (B.inclusion.map (s.inclusion i)).base := by
    rw [← s.covers]
    trivial
  obtain ⟨i, z, hz⟩ := Set.mem_iUnion.mp hx
  have hrestr : (∏ j, n j) • (𝟙
      (((smallEtaleBaseChange B (s.inclusion i)).sheafPullback AddCommGrpCat.{u + 1}
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B (s.piece i).obj (s.piece i).property)).obj F)) = 0 := by
    obtain ⟨d, hd⟩ := Finset.dvd_prod_of_mem n (Finset.mem_univ i)
    rw [hd, mul_nsmul, hann i, smul_zero]
  set t' := GeometricPoint.ofPoint (s.piece i).obj z
  have hbase : (t'.map (B.inclusion.map (s.inclusion i))).hom default = t.hom default := by
    show (B.inclusion.map (s.inclusion i)).base (t'.hom default) = t.hom default
    rwa [show t'.hom default = z from GeometricPoint.ofPoint_liesOver (s.piece i).obj z]
  refine AddCommGrpCat.nsmul_eq_zero_of_iso
    ((etaleStalkPresheafFunctorIsoOfEqBase B X.obj X.property hbase
      AddCommGrpCat.{u + 1}).app F.obj) _ (fun y => ?_) g
  refine AddCommGrpCat.nsmul_eq_zero_of_iso
    (etaleStalkSmallEtalePullObjIso B (s.inclusion i) t' AddCommGrpCat.{u + 1} F) _
    (fun x => ?_) y
  exact SmallEtale.nsmul_etaleStalk_eq_zero_of_nsmul_id_eq_zero B (s.piece i).obj
    (s.piece i).property t' _ _ hrestr x

/-! ### The integral presentation -/

/-- **The generators correspond.** The sheaf of `ℤ`-modules attached to `j_{U!}\underline{ULift ℤ}`
is the extension by zero of the constant free rank-one `ℤ`-module sheaf at `U`.

Both sides are the inverse image along `U → X` of a constant sheaf, so the comparison is the
compatibility of the inverse image and of the constant sheaf with a change of coefficients —
`CategoryTheory.Sheaf.sheafPullbackCoefficientIso` and
`CategoryTheory.Sheaf.constantSheafCoefficientIso` — together with the identification of the two
constant values, which is the counit of the equivalence between abelian groups and
`ℤ`-modules. -/
public def abelianShriekConstantIntIso (U : SmallEtale B X.obj X.property) :
    (sheafCompose (SmallEtale.topology B X.obj X.property)
        AddCommGrpCat.moduleCatIntEquivalence.{u + 1}.functor).obj
        (abelianShriekConstant B X (AddCommGrpCat.of (ULift.{u + 1} ℤ)) U) ≅
      moduleShriekConstant.{u, 0, u + 1} B X ℤ U := by
  let := SmallEtale.hasSheafify_moduleCat.{u, 0, u + 1} B X ℤ
  let := SmallEtale.hasSheafify_moduleCat.{u, 0, u + 1} B U.obj.left ℤ
  let := (SmallEtale.finalIsTerminal B U.obj.left.obj U.obj.left.property).hasTerminal
  refine (sheafCompose (SmallEtale.topology B X.obj X.property)
      AddCommGrpCat.moduleCatIntEquivalence.{u + 1}.functor).mapIso
    (((Functor.sheafPullbackConstruction.sheafPullbackIso
      (smallEtalePostcompose B X.obj X.property U) AddCommGrpCat.{u + 1}
      (SmallEtale.topology B U.obj.left.obj U.obj.left.property)
      (SmallEtale.topology B X.obj X.property)).app _).symm) ≪≫ ?_
  refine (Sheaf.sheafPullbackCoefficientIso (smallEtalePostcompose B X.obj X.property U)
    (SmallEtale.topology B U.obj.left.obj U.obj.left.property)
    (SmallEtale.topology B X.obj X.property)
    AddCommGrpCat.moduleCatIntEquivalence.{u + 1}).app _ ≪≫ ?_
  refine ((smallEtalePostcompose B X.obj X.property U).sheafPullback (ModuleCat.{u + 1} ℤ)
      (SmallEtale.topology B U.obj.left.obj U.obj.left.property)
      (SmallEtale.topology B X.obj X.property)).mapIso
    ((Sheaf.constantSheafCoefficientIso
        (SmallEtale.topology B U.obj.left.obj U.obj.left.property)
        AddCommGrpCat.moduleCatIntEquivalence.{u + 1}).app _ ≪≫
      (constantSheaf (SmallEtale.topology B U.obj.left.obj U.obj.left.property)
        (ModuleCat.{u + 1} ℤ)).mapIso
          (AddCommGrpCat.moduleCatIntEquivalence.{u + 1}.counitIso.app
            (ModuleCat.of ℤ (ULift.{u + 1} ℤ)))) ≪≫ ?_
  exact (Functor.sheafPullbackConstruction.sheafPullbackIso
    (smallEtalePostcompose B X.obj X.property U) (ModuleCat.{u + 1} ℤ)
    (SmallEtale.topology B U.obj.left.obj U.obj.left.property)
    (SmallEtale.topology B X.obj X.property)).app _

/-- **A constructible abelian sheaf is a finite cokernel of extensions by zero of the constant
sheaf `ℤ` at affine étale objects.** This is the forward half of Stacks 095N at `Λ = ℤ`, read for
abelian sheaves: abelian groups are `ℤ`-modules, the forward half at `ℤ` is
`AlgebraicGeometry.hasFiniteShriekPresentation_int_of_uliftInt` fed by the affine form of the
library's Stacks 095N, and the presentation is carried back along the equivalence of coefficients,
whose generators correspond by `AlgebraicGeometry.abelianShriekConstantIntIso`. -/
public theorem exists_affine_abelianShriekIntPresentation_of_isConstructibleAbelianSheaf
    (hXc : CompactSpace X.obj) (hXq : QuasiSeparatedSpace X.obj)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hF : IsConstructibleAbelianSheaf B X F) :
    ∃ (n m : ℕ) (U : Fin n → SmallEtale B X.obj X.property)
      (V : Fin m → SmallEtale B X.obj X.property),
      (∀ i, SmallEtale.IsAffine B X.obj X.property (U i)) ∧
      (∀ j, SmallEtale.IsAffine B X.obj X.property (V j)) ∧
      ∃ f : (∐ fun j => abelianShriekConstant B X (AddCommGrpCat.of (ULift.{u + 1} ℤ)) (V j)) ⟶
          (∐ fun i => abelianShriekConstant B X (AddCommGrpCat.of (ULift.{u + 1} ℤ)) (U i)),
        Nonempty (cokernel f ≅ F) := by
  let : ∀ (S T : B.Scheme) (f : T ⟶ S),
      ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{u + 1} ℤ)
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).IsRightAdjoint := fun _ _ _ =>
    Sheaf.isRightAdjoint_sheafPushforwardContinuous_of_coefficientEquivalence _ _ _
      AddCommGrpCat.moduleCatIntEquivalence.{u + 1}
  let : ∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
      HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
        (ModuleCat.{u + 1} ℤ) := fun _ _ =>
    Sheaf.hasWeakSheafify_of_coefficientEquivalence _
      AddCommGrpCat.moduleCatIntEquivalence.{u + 1}
  let : ∀ (S T : B.Scheme) (f : T ⟶ S),
      ((smallEtaleBaseChange B f).sheafPushforwardContinuous
          (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).IsRightAdjoint := fun _ _ _ =>
    Sheaf.isRightAdjoint_sheafPushforwardContinuous_of_coefficientEquivalence _ _ _
      AddCommGrpCat.moduleCatUliftIntEquivalence.{u + 1, u + 1}
  let : ∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
      HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
        (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) := fun _ _ =>
    Sheaf.hasWeakSheafify_of_coefficientEquivalence _
      AddCommGrpCat.moduleCatUliftIntEquivalence.{u + 1, u + 1}
  let := SmallEtale.hasSheafify_moduleCat.{u, 0, u + 1} B X ℤ
  set E := Sheaf.coefficientEquivalence (SmallEtale.topology B X.obj X.property)
    AddCommGrpCat.moduleCatIntEquivalence.{u + 1}
  have hG : IsConstructibleModuleSheaf B X ℤ (E.functor.obj F) :=
    isConstructibleModuleSheaf_moduleCatIntEquivalence B X F hF
  have hpres : HasFiniteShriekPresentation.{u, 0, u + 1} B X ℤ
      (SmallEtale.IsAffine B X.obj X.property) (E.functor.obj F) :=
    hasFiniteShriekPresentation_int_of_uliftInt B X _ _
      ((isConstructibleModuleSheaf_iff_hasFiniteAffineShriekPresentation B X
        (ULift.{u + 1} ℤ) _).1 (isConstructibleModuleSheaf_uliftIntRestrictScalars B X _ hG))
  have : E.inverse.Additive := by
    constructor
    intro F₁ F₂ p q
    ext V : 3
    rfl
  obtain ⟨n, m, Us, Vs, hU, hV, f, ⟨ef⟩⟩ := hpres
  have η : ∀ W : SmallEtale B X.obj X.property,
      E.inverse.obj (moduleShriekConstant.{u, 0, u + 1} B X ℤ W) ≅
        abelianShriekConstant B X (AddCommGrpCat.of (ULift.{u + 1} ℤ)) W := fun W =>
    (E.unitIso.app _ ≪≫ E.inverse.mapIso (abelianShriekConstantIntIso B X W)).symm
  have σ : ∀ {k : ℕ} (W : Fin k → SmallEtale B X.obj X.property),
      E.inverse.obj (∐ fun i => moduleShriekConstant.{u, 0, u + 1} B X ℤ (W i)) ≅
        ∐ fun i => abelianShriekConstant B X (AddCommGrpCat.of (ULift.{u + 1} ℤ)) (W i) :=
    fun W => PreservesCoproduct.iso E.inverse _ ≪≫ Sigma.mapIso fun i => η (W i)
  have eG : cokernel f ≅ E.functor.obj F :=
    (sheafToPresheaf (SmallEtale.topology B X.obj X.property)
        (ModuleCat.{u + 1} ℤ)).preimageIso
      (ef ≪≫ Functor.isoWhiskerLeft _ (ModuleCat.uliftFunctorSelfIso.{0, u + 1} ℤ) ≪≫
        Functor.rightUnitor _)
  refine ⟨n, m, Us, Vs, hU, hV, (σ Vs).inv ≫ E.inverse.map f ≫ (σ Us).hom, ⟨?_⟩⟩
  exact cokernel.mapIso _ (E.inverse.map f) (σ Vs).symm (σ Us).symm (by simp) ≪≫
    (PreservesCokernel.iso E.inverse f).symm ≪≫ E.inverse.mapIso eG ≪≫ (E.unitIso.app F).symm

/-! ### Stacks 09YT -/

/-- **A constructible abelian sheaf on a quasi-compact quasi-separated scheme has a presentation
by the sheaves `j_{U!}(Z/NZ)` at affine étale objects.** The integral presentation of the sheaf is
quotiented by an integer `N` annihilating it: that leaves the sheaf unchanged, because a cokernel
annihilated by `N` is also the cokernel of the induced map between the quotients by `N`, and it
replaces the constant value `ULift ℤ` of each generator by `ULift (Z/NZ)`. -/
public theorem hasFiniteZModShriekPresentation_of_isConstructibleAbelianSheaf
    (hXc : CompactSpace X.obj) (hXq : QuasiSeparatedSpace X.obj)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hF : IsConstructibleAbelianSheaf B X F) :
    HasFiniteZModShriekPresentation B X (SmallEtale.IsAffine B X.obj X.property) F := by
  obtain ⟨N, hN, hann⟩ :=
    exists_nsmul_id_eq_zero_of_isConstructibleAbelianSheaf B X hXc hXq F hF
  obtain ⟨n, m, Us, Vs, hU, hV, f, ⟨e⟩⟩ :=
    exists_affine_abelianShriekIntPresentation_of_isConstructibleAbelianSheaf B X hXc hXq F hF
  let e' {k : ℕ} (W : Fin k → SmallEtale B X.obj X.property) :=
    Limits.cokernelNsmulCoproductIso
      (fun i => abelianShriekConstant B X (AddCommGrpCat.of (ULift.{u + 1} ℤ)) (W i)) N ≪≫
    Sigma.mapIso fun i => cokernelNsmulAbelianShriekZModIso B X (W i) N
  let eU := e' Us
  let eV := e' Vs
  obtain ⟨g, ⟨eg⟩⟩ := Limits.exists_cokernel_nsmul_of_nsmul_id_eq_zero f e N hann
  refine ⟨n, m, Us, Vs, fun _ => N, fun _ => N, hU, hV, fun _ => hN, fun _ => hN,
    eV.inv ≫ g ≫ eU.hom, ⟨?_⟩⟩
  exact (cokernel.mapIso g (eV.inv ≫ g ≫ eU.hom) eV eU (by simp)).symm ≪≫ eg

/-- **Stacks 09YT.** Let `X` be a quasi-compact and quasi-separated scheme. An abelian sheaf on the
small étale site of `X` is constructible exactly when it is of the form
`Coker(⨁_j j_{V_j!}(Z/m_jZ) → ⨁_i j_{U_i!}(Z/n_iZ))` with the `V_j` and `U_i` quasi-compact
quasi-separated objects of `X_étale` and the `m_j`, `n_i` positive integers.

Both inclusions are proved. A cokernel of that form is constructible because constructibility of
abelian sheaves is a weak Serre condition, Stacks 03RZ (2), and the summands are constructible by
Stacks 03S8 (2) at the finite groups `Z/nZ`, which is
`AlgebraicGeometry.abelianShriekZModIsConstructible`. Conversely a constructible abelian sheaf is
annihilated by a positive integer `N` and has a presentation by extensions by zero of the constant
sheaf `ℤ` from Stacks 095N at `Λ = ℤ`; quotienting that presentation by `N` turns it into one of
the displayed form. -/
@[stacks 09YT "a constructible abelian sheaf on a quasi-compact quasi-separated scheme is exactly \
a cokernel of a map between finite direct sums of the sheaves j_{U!}(Z/nZ) at quasi-compact \
quasi-separated etale objects and positive integers n"]
public theorem isConstructibleAbelianSheaf_iff_hasFiniteZModShriekPresentation
    (hXc : CompactSpace X.obj) (hXq : QuasiSeparatedSpace X.obj)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) :
    IsConstructibleAbelianSheaf B X F ↔
      HasFiniteZModShriekPresentation B X (IsQCQSEtaleObject B X) F :=
  ⟨fun hF => hasFiniteZModShriekPresentation_qcqs_of_affine B X
      (hasFiniteZModShriekPresentation_of_isConstructibleAbelianSheaf B X hXc hXq F hF),
    isConstructibleAbelianSheaf_of_zModShriekPresentation B X _
      fun U n hU hn => abelianShriekZModIsConstructible B X U n hn hXc hXq hU⟩

/-- **Stacks 09YT, the affine form.** "In fact, we can even assume `U_i` and `V_j` affine": the
étale objects of the presentation of a constructible abelian sheaf may be taken affine, and a
presentation by affine objects still has a constructible cokernel. -/
@[stacks 09YT "the same characterization with the etale objects of the presentation affine, which \
is the tag's concluding sentence"]
public theorem isConstructibleAbelianSheaf_iff_affineZModShriekPresentation
    (hXc : CompactSpace X.obj) (hXq : QuasiSeparatedSpace X.obj)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) :
    IsConstructibleAbelianSheaf B X F ↔
      HasFiniteZModShriekPresentation B X (SmallEtale.IsAffine B X.obj X.property) F :=
  ⟨hasFiniteZModShriekPresentation_of_isConstructibleAbelianSheaf B X hXc hXq F,
    isConstructibleAbelianSheaf_of_zModShriekPresentation B X _ fun U n hU hn =>
      abelianShriekZModIsConstructible B X U n hn hXc hXq
        (by have := hU; exact ⟨inferInstance, inferInstance⟩)⟩

end AlgebraicGeometry

end
