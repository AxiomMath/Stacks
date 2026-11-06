module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FundamentalGroupLocallyConstant.Abelian

/-!
# The geometric fibre of a finite locally constant sheaf, with its monodromy action

Let `X` be a connected scheme in a big étale site `B` and `x` a geometric point of `X`. A finite
locally constant sheaf of sets on `X_étale` is represented by a finite étale cover (Tag 03RV),
whose geometric fibre at `x` carries the action of `π₁(X, x)` of Tag 0BND. This file records the
resulting equivalence of Tag 0DV5 (1) *explicitly*, as the composite of the two dictionaries, so
that the finite `π₁(X, x)`-set attached to a sheaf is, element for element, the geometric fibre
of its representing cover, and the action is evaluation of natural automorphisms of the fibre
functor; and the equivalence of Tag 0DV5 (2) built from it.

## Main definitions

* `AlgebraicGeometry.geometricFibreSetEquivalence`: the explicit equivalence of Tag 0DV5 (1).
* `AlgebraicGeometry.geometricFibreAbelianEquivalence`: the equivalence of Tag 0DV5 (2) built
  from it.
* `AlgebraicGeometry.geometricFibreSetEquiv`: the underlying set of the `π₁(X, x)`-set attached
  to a sheaf is the geometric fibre of its representing cover.

## Implementation notes

The library's `AlgebraicGeometry.finiteLocallyConstantSetsEquivalence` is obtained by choice
from an existence statement and so forgets how its underlying sets are the geometric fibres;
consumers comparing the fibres of two sheaves (for instance of a sheaf and of its inverse image
along a finite étale cover, through Tag 0BND (3)) need the explicit composite recorded here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.ConstantSheaf
open scoped FintypeCatDiscrete ZeroObject

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)

/-- **Tag 0DV5 (1), explicitly.** The finite locally constant sheaves of sets on `X_étale` are
the finite continuous `π₁(X, x)`-sets, by representing a sheaf by a finite étale cover (Tag 03RV)
and taking the geometric fibre of the cover at `x` with its monodromy action (Tag 0BND (1)). -/
def geometricFibreSetEquivalence :
    (isFiniteLocallyConstantSetSheaf.{u, u + 1, u + 1}
        (SmallEtale.topology B X.1 X.2)).FullSubcategory ≌
      (ContinuousGSet.isFinite.{u + 1, u + 1} (EtaleFundamentalGroup X.1 x)).FullSubcategory :=
  (finiteLocallyConstantFiniteEtaleEquivalence B X).trans
    ((finiteEtaleEquivalenceOfIsGaloisCategory X.1 x).trans
      ((contActionUniverseEquivalence.{u, u + 1} (EtaleFundamentalGroup X.1 x)).trans
        finiteContinuousGSetEquivalence.symm))

/-- **Tag 0DV5 (2), built from the explicit form of part (1).** The finite locally constant
abelian sheaves on `X_étale` are the finite discrete `π₁(X, x)`-modules; the underlying
`π₁(X, x)`-set of the module attached to a sheaf is the geometric fibre of the cover
representing its underlying sheaf of sets. -/
def geometricFibreAbelianEquivalence :
    (isFiniteLocallyConstantAbelianSheaf.{u, u + 1, u + 1}
        (SmallEtale.topology B X.1 X.2)).FullSubcategory ≌
      (ContinuousGAddCommGrp.isFinite.{u + 1, u + 1}
        (EtaleFundamentalGroup X.1 x)).FullSubcategory :=
  finiteLocallyConstantAbelianEquivalenceOfSetEquivalence
    (SmallEtale.topology B X.1 X.2) (EtaleFundamentalGroup X.1 x)
    (geometricFibreSetEquivalence B X x)

/-- The equivalence of Tag 0DV5 (2) built from the explicit form of part (1) is additive. -/
instance additive_geometricFibreAbelianEquivalence :
    (geometricFibreAbelianEquivalence B X x).functor.Additive := by
  set e := geometricFibreAbelianEquivalence B X x
  let : HasZeroObject
      (ContinuousGAddCommGrp.isFinite.{u + 1, u + 1}
        (EtaleFundamentalGroup X.1 x)).FullSubcategory :=
    ⟨⟨e.functor.obj 0, isZero_equivalence_functor_obj e (isZero_zero _)⟩⟩
  let : e.functor.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_map_zero_object
      ((isZero_equivalence_functor_obj e (isZero_zero _)).iso (isZero_zero _))
  exact Functor.additive_of_preserves_binary_products e.functor

/-- The finite étale cover representing a finite locally constant sheaf of sets. -/
abbrev representingCover :
    (isFiniteLocallyConstantSetSheaf.{u, u + 1, u + 1}
        (SmallEtale.topology B X.1 X.2)).FullSubcategory ⥤ FiniteEtaleOver X.1 :=
  (finiteLocallyConstantFiniteEtaleEquivalence B X).functor

/-- **The underlying set of the `π₁(X, x)`-set attached to a sheaf is the geometric fibre of its
representing cover.** -/
def geometricFibreSetEquiv
    (Y : (isFiniteLocallyConstantSetSheaf.{u, u + 1, u + 1}
      (SmallEtale.topology B X.1 X.2)).FullSubcategory) :
    ((geometricFibreSetEquivalence B X x).functor.obj Y).obj.obj.obj.V ≃
      (finiteEtaleFiberFunctor x).obj ((representingCover B X).obj Y) :=
  FintypeCat.uSwitchEquiv _

/-- The equivalence `geometricFibreSetEquiv` intertwines the action of `π₁(X, x)` on the
`π₁(X, x)`-set attached to a sheaf with evaluation of natural automorphisms of the fibre functor
on its representing cover. -/
theorem geometricFibreSetEquiv_smul
    (Y : (isFiniteLocallyConstantSetSheaf.{u, u + 1, u + 1}
      (SmallEtale.topology B X.1 X.2)).FullSubcategory) (σ : EtaleFundamentalGroup X.1 x)
    (a : ((geometricFibreSetEquivalence B X x).functor.obj Y).obj.obj.obj.V) :
    geometricFibreSetEquiv B X x Y
        (((geometricFibreSetEquivalence B X x).functor.obj Y).obj.obj.obj.ρ σ a) =
      (σ.asIso.app ((representingCover B X).obj Y)).hom (geometricFibreSetEquiv B X x Y a) := by
  refine (FintypeCat.uSwitchEquiv_naturality
    (((finiteEtaleEquivalenceOfIsGaloisCategory X.1 x).functor.obj
      ((representingCover B X).obj Y)).obj.ρ σ).asHom a).symm.trans ?_
  exact finiteEtaleEquivalenceOfIsGaloisCategory_action X.1 x _ σ _

/-- The equivalence `geometricFibreSetEquiv` is natural in the sheaf. -/
theorem geometricFibreSetEquiv_naturality
    {Y Y' : (isFiniteLocallyConstantSetSheaf.{u, u + 1, u + 1}
      (SmallEtale.topology B X.1 X.2)).FullSubcategory} (f : Y ⟶ Y')
    (a : ((geometricFibreSetEquivalence B X x).functor.obj Y).obj.obj.obj.V) :
    geometricFibreSetEquiv B X x Y'
        (((geometricFibreSetEquivalence B X x).functor.map f).hom.hom.hom a) =
      (finiteEtaleFiberFunctor x).map ((representingCover B X).map f)
        (geometricFibreSetEquiv B X x Y a) :=
  (FintypeCat.uSwitchEquiv_naturality _ a).symm

section TrivialCover

variable {Y : Scheme.{u}} (y : GeometricPoint Y) (ι : Type u) [Finite ι]

/-- The identity of `Y`, as a finite étale cover of `Y`: the terminal cover. -/
abbrev terminalCover (Y : Scheme.{u}) : FiniteEtaleOver Y :=
  MorphismProperty.Over.mk ⊤ (𝟙 Y) (MorphismProperty.id_mem _ _)

/-- The trivial cover `∐_{i : ι} Y ⟶ Y`, the disjoint union of copies of the terminal cover. -/
abbrev trivialCover : FiniteEtaleOver Y :=
  (Stacks.FundamentalGroup.sigmaCocone Y (Discrete.functor fun _ : ι ↦ terminalCover Y)).pt

/-- The geometric fibre of the terminal cover is a single point. -/
instance subsingleton_finiteEtaleFiber_terminalCover :
    Subsingleton ((finiteEtaleFiberFunctor y).obj (terminalCover Y)) :=
  ⟨fun a b ↦ Subtype.ext (by
    have : Mono (terminalCover Y).hom := inferInstanceAs (Mono (𝟙 Y))
    exact (cancel_mono (terminalCover Y).hom).mp (a.2.trans b.2.symm))⟩

/-- **The geometric fibre of the trivial cover `∐_{i : ι} Y` is `ι`, with trivial monodromy.**
The fibre functor preserves the finite coproduct, and the fibre of each copy of `Y` is a single
point fixed by every natural automorphism. -/
theorem card_finiteEtaleFiber_trivialCover_and_smul [ConnectedSpace Y] :
    Nat.card ((finiteEtaleFiberFunctor y).obj (trivialCover ι)) = Nat.card ι ∧
      ∀ (σ : EtaleFundamentalGroup Y y) (a : (finiteEtaleFiberFunctor y).obj (trivialCover ι)),
        (σ.asIso.app (trivialCover ι)).hom a = a := by
  classical
  have := Fintype.ofFinite ι
  have := Stacks.FundamentalGroup.preservesFiniteColimits_finiteEtaleFiberFunctor y
  let c := Stacks.FundamentalGroup.sigmaCocone Y (Discrete.functor fun _ : ι ↦ terminalCover Y)
  have hc : IsColimit (Cofan.mk c.pt fun i ↦ c.ι.app ⟨i⟩) :=
    Stacks.FundamentalGroup.isColimitSigmaCocone Y _
  have hc' := isColimitCofanMkObjOfIsColimit (finiteEtaleFiberFunctor y) _ _ hc
  let p₀ : (finiteEtaleFiberFunctor y).obj (terminalCover Y) := ⟨y.hom, Category.comp_id _⟩
  have hp (b : (finiteEtaleFiberFunctor y).obj (terminalCover Y)) : b = p₀ :=
    Subsingleton.elim _ _
  let pts : ι → (finiteEtaleFiberFunctor y).obj (trivialCover ι) :=
    fun i ↦ (finiteEtaleFiberFunctor y).map (c.ι.app ⟨i⟩) p₀
  have hsurj : Function.Surjective pts := fun a ↦ by
    obtain ⟨i, b, hb⟩ := Cofan.inj_jointly_surjective_of_isColimit hc' a
    refine ⟨i, ?_⟩
    rw [← hb, hp b]
    rfl
  have hinj : Function.Injective pts := fun i j h ↦
    Cofan.eq_of_inj_apply_eq_of_isColimit hc' p₀ p₀ h
  refine ⟨(Nat.card_congr (Equiv.ofBijective pts ⟨hinj, hsurj⟩)).symm, fun σ a ↦ ?_⟩
  obtain ⟨i, rfl⟩ := hsurj a
  have hn := congrArg (fun f ↦ f p₀) (σ.asIso.hom.naturality (c.ι.app ⟨i⟩))
  simp only [types_comp_apply] at hn
  show σ.asIso.hom.app (trivialCover ι) ((finiteEtaleFiberFunctor y).map (c.ι.app ⟨i⟩) p₀) =
    (finiteEtaleFiberFunctor y).map (c.ι.app ⟨i⟩) p₀
  refine hn.trans ?_
  congr 1
  exact hp _

end TrivialCover

end AlgebraicGeometry

end
