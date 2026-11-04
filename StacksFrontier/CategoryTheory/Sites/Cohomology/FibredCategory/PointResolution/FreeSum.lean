module

public import StacksFrontier.CategoryTheory.Sites.CechNerveHomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.ProjectionLowerShriek
public import StacksFrontier.Algebra.Homology.DerivedCategory.UnboundedComplexes

/-!
# Free abelian presheaves on coproducts of representables

This file defines the class of abelian presheaves on the total category of a fibred category
situation that are free on a coproduct of (universe-lifted) representable presheaves. It shows
that the class contains zero, is closed under binary direct sums and resolves every abelian
presheaf, and that sheafification carries it into the class of direct sums of the free abelian
sheaves `j_{x!} ℤ_x`.

## Main definitions

* `Stacks.Sites.FibredCategory.FibredCategorySituation.sigmaYoneda`: `y ↦ ∐_i Hom(y, x_i)`.
* `Stacks.Sites.FibredCategory.FibredCategorySituation.IsFreeSum`: the abelian presheaves free
  on a coproduct of representables.

## Main results

* `Stacks.Sites.FibredCategory.FibredCategorySituation.exists_isFreeSum_resolution`: every abelian
  presheaf has a bounded above resolution by members of the class.
* `Stacks.Sites.FibredCategory.FibredCategorySituation.isSumOfExtensionByZeroUnitsAb_sheafify`:
  the sheafification of a member of the class is a direct sum of the sheaves `j_{x!} ℤ_x`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe uD vD uC vC w

namespace Stacks.Sites.FibredCategory.FibredCategorySituation

variable (s : FibredCategorySituation.{uD, vD, uC, vC, w})

/-- The presheaf of sets `y ↦ ∐_i Hom(y, x_i)`, with the morphism sets lifted to the universe of
the sections. -/
@[simps]
def sigmaYoneda {ι : Type (max w uD vD uC vC)} (x : ι → s.C) :
    s.Cᵒᵖ ⥤ Type (max w uD vD uC vC) where
  obj y := Σ i, ULift.{max w uD vD uC} (y.unop ⟶ x i)
  map f := ↾fun g => ⟨g.1, ⟨f.unop ≫ g.2.down⟩⟩
  map_id _ := by ext ⟨i, g⟩ <;> first | rfl | exact heq_of_eq (by simp)
  map_comp _ _ := by ext ⟨i, g⟩ <;> first | rfl | exact heq_of_eq (by simp)

/-- The abelian presheaves which are free on a coproduct of representables. -/
def IsFreeSum : ObjectProperty (s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC vC}) := fun G =>
  ∃ (ι : Type (max w uD vD uC vC)) (x : ι → s.C),
    Nonempty (Presheaf.freeAbelian.obj (sigmaYoneda s x) ≅ G)

/-- The inclusion of the `i`th summand into `sigmaYoneda`. -/
@[simps]
def sigmaYonedaι {ι : Type (max w uD vD uC vC)} (x : ι → s.C) (i : ι) :
    uliftYoneda.{max w uD vD uC}.obj (x i) ⟶ sigmaYoneda s x where
  app _ := ↾fun g => ⟨i, g⟩
  naturality _ _ _ := rfl

/-- `sigmaYoneda` is the coproduct of the lifted representable presheaves. -/
def isColimitSigmaYoneda {ι : Type (max w uD vD uC vC)} (x : ι → s.C) :
    IsColimit (Cofan.mk (sigmaYoneda s x) (sigmaYonedaι s x)) :=
  Cofan.IsColimit.mk _
    (fun t => { app := fun y => ↾fun g => (t.inj g.1).app y g.2
                naturality := fun y y' f => by
                  ext ⟨i, g⟩
                  exact ConcreteCategory.congr_hom ((t.inj i).naturality f) g })
    (fun t i => by ext y g; rfl)
    (fun t m hm => by
      ext y ⟨i, g⟩
      exact ConcreteCategory.congr_hom (NatTrans.congr_app (hm i) y) g)

/-- The free abelian presheaf on `sigmaYoneda` is the coproduct of the free abelian presheaves on
the lifted representables. -/
def freeSigmaYonedaIso {ι : Type (max w uD vD uC vC)} (x : ι → s.C) :
    Presheaf.freeAbelian.obj (sigmaYoneda s x) ≅
      ∐ fun i => Presheaf.freeAbelian.{max w uD vD uC vC}.obj
        (uliftYoneda.{max w uD vD uC}.obj (x i)) :=
  (isColimitCofanMkObjOfIsColimit Presheaf.freeAbelian _ _
      (isColimitSigmaYoneda s x)).coconePointUniqueUpToIso
    (coproductIsCoproduct _)

/-- A free abelian presheaf on a coproduct of representables is, up to isomorphism, the
coproduct of the free abelian presheaves on the representables. -/
lemma isFreeSum_iff (G : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC vC}) :
    IsFreeSum s G ↔ ∃ (ι : Type (max w uD vD uC vC)) (x : ι → s.C),
      Nonempty ((∐ fun i => Presheaf.freeAbelian.{max w uD vD uC vC}.obj
        (uliftYoneda.{max w uD vD uC}.obj (x i))) ≅ G) := by
  constructor
  · rintro ⟨ι, x, ⟨e⟩⟩
    exact ⟨ι, x, ⟨(freeSigmaYonedaIso s x).symm ≪≫ e⟩⟩
  · rintro ⟨ι, x, ⟨e⟩⟩
    exact ⟨ι, x, ⟨freeSigmaYonedaIso s x ≪≫ e⟩⟩

/-- The class of free abelian presheaves on coproducts of representables contains a zero object:
the free abelian presheaf on the empty coproduct. -/
instance containsZero_isFreeSum : (IsFreeSum s).ContainsZero := by
  let x : PEmpty.{max w uD vD uC vC + 1} → s.C := fun i => nomatch i
  refine ⟨⟨Presheaf.freeAbelian.obj (sigmaYoneda s x), Functor.isZero _ fun y => ?_,
    PEmpty, x, ⟨Iso.refl _⟩⟩⟩
  have : IsEmpty ((sigmaYoneda s x).obj y) := ⟨fun g => nomatch g.1⟩
  exact @AddCommGrpCat.isZero_of_subsingleton _
    (inferInstanceAs (Subsingleton (FreeAbelianGroup ((sigmaYoneda s x).obj y))))

/-- The class of free abelian presheaves on coproducts of representables is closed under binary
direct sums. -/
lemma isFreeSum_biprod {F G : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC vC}}
    (hF : IsFreeSum s F) (hG : IsFreeSum s G) : IsFreeSum s (F ⊞ G) := by
  rw [isFreeSum_iff] at hF hG ⊢
  obtain ⟨ι, U, ⟨eF⟩⟩ := hF
  obtain ⟨κ, V, ⟨eG⟩⟩ := hG
  refine ⟨ι ⊕ κ, Sum.elim U V, ?_⟩
  let A' : ι → s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC vC} :=
    fun i => Presheaf.freeAbelian.obj (uliftYoneda.{max w uD vD uC}.obj (U i))
  let B' : κ → s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC vC} :=
    fun j => Presheaf.freeAbelian.obj (uliftYoneda.{max w uD vD uC}.obj (V j))
  have hAB : (fun i : ι ⊕ κ => Presheaf.freeAbelian.{max w uD vD uC vC}.obj
      (uliftYoneda.{max w uD vD uC}.obj (Sum.elim U V i))) = Sum.elim A' B' := by
    funext i
    cases i <;> rfl
  let e : Discrete.functor (fun i : ι ⊕ κ => Presheaf.freeAbelian.{max w uD vD uC vC}.obj
      (uliftYoneda.{max w uD vD uC}.obj (Sum.elim U V i))) ≅ Discrete.functor (Sum.elim A' B') :=
    NatIso.ofComponents (fun i => eqToIso (congrFun hAB i.as)) (by
      intro i j f
      cases f
      cat_disch)
  exact ⟨HasColimit.isoOfNatIso e ≪≫
    (coproductIsCoproduct (Sum.elim A' B')).coconePointUniqueUpToIso
      (Cofan.combPairIsColimit (coproductIsCoproduct A') (coproductIsCoproduct B')
        (coprodIsCoprod (∐ A') (∐ B'))) ≪≫
    (biprod.isoCoprod (∐ A') (∐ B')).symm ≪≫ biprod.mapIso eF eG⟩

/-- **Every abelian presheaf is a quotient of a free abelian presheaf on a coproduct of
representables.** -/
lemma exists_epi_isFreeSum (G : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC vC}) :
    ∃ (F : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC vC}) (_ : IsFreeSum s F) (π : F ⟶ G), Epi π := by
  let ι : Type (max w uD vD uC vC) := Σ y : s.C, (G.obj (op y) : Type (max w uD vD uC vC))
  let x : ι → s.C := fun i => i.1
  let π : Presheaf.freeAbelian.obj (sigmaYoneda s x) ⟶ G :=
    { app := fun y => AddCommGrpCat.ofHom
        (FreeAbelianGroup.lift fun g : (sigmaYoneda s x).obj y => G.map g.2.down.op g.1.2)
      naturality := fun y y' f => by
        ext z
        show (FreeAbelianGroup.lift fun g : (sigmaYoneda s x).obj y' => G.map g.2.down.op g.1.2)
            (FreeAbelianGroup.map _ z) =
          G.map f ((FreeAbelianGroup.lift fun g : (sigmaYoneda s x).obj y =>
            G.map g.2.down.op g.1.2) z)
        induction z using FreeAbelianGroup.induction_on with
        | zero => simp
        | of g =>
          rw [FreeAbelianGroup.map_of_apply, FreeAbelianGroup.lift_apply_of,
            FreeAbelianGroup.lift_apply_of]
          show G.map (f.unop ≫ g.2.down).op g.1.2 = G.map f (G.map g.2.down.op g.1.2)
          rw [op_comp, Functor.map_comp, Quiver.Hom.op_unop]
          rfl
        | neg g ih => simp only [map_neg, ih]
        | add a b ha hb => simp only [map_add, ha, hb] }
  refine ⟨_, ⟨ι, x, ⟨Iso.refl _⟩⟩, π, ?_⟩
  have : ∀ y, Epi (π.app y) := fun y => by
    rw [AddCommGrpCat.epi_iff_surjective]
    exact fun t => ⟨FreeAbelianGroup.of ⟨⟨y.unop, t⟩, ⟨𝟙 _⟩⟩, (FreeAbelianGroup.lift_apply_of
      (fun g : (sigmaYoneda s x).obj y => G.map g.2.down.op g.1.2) _).trans
        (by change G.map (𝟙 y.unop).op t = t; simp)⟩
  exact NatTrans.epi_of_epi_app _

/-- **The sheafification of a free abelian presheaf on a coproduct of representables is a direct
sum of the free abelian sheaves `j_{x!} ℤ_x`.** -/
lemma isSumOfExtensionByZeroUnitsAb_sheafify {G : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC vC}}
    (hG : IsFreeSum s G) :
    Stacks.Cohomology.DerivedLowerShriek.IsSumOfExtensionByZeroUnitsAb.{max w uD vD uC}
      s.topology ((presheafToSheaf s.topology AddCommGrpCat.{max w uD vD uC vC}).obj G) := by
  rw [isFreeSum_iff] at hG
  obtain ⟨ι, x, ⟨e⟩⟩ := hG
  have hshape :=
    Stacks.Cohomology.DerivedLowerShriek.hasColimitsOfShape_discrete_sheafAb.{max w uD vD uC vC}
      s.topology ι
  have hcop : HasCoproduct fun i =>
      Stacks.Cohomology.DerivedLowerShriek.extensionByZeroUnitAb.{max w uD vD uC} s.topology
        (x i) := hshape.has_colimit _
  have hpres : PreservesColimitsOfShape (Discrete ι)
      (presheafToSheaf s.topology AddCommGrpCat.{max w uD vD uC vC}) :=
    (sheafificationAdjunction s.topology
      AddCommGrpCat.{max w uD vD uC vC}).leftAdjoint_preservesColimits.preservesColimitsOfShape
  exact ⟨ι, x, ⟨(PreservesCoproduct.iso (presheafToSheaf s.topology _) _).symm ≪≫
    (presheafToSheaf s.topology AddCommGrpCat.{max w uD vD uC vC}).mapIso e⟩⟩

/-- **Every abelian presheaf has a resolution by free abelian presheaves on coproducts of
representables**, bounded above by `0`. -/
lemma exists_isFreeSum_resolution (G : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC vC}) :
    ∃ (Q : CochainComplex (s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC vC}) ℤ) (_ : Q.IsStrictlyLE 0)
      (_ : ∀ n, IsFreeSum s (Q.X n))
      (π : Q ⟶ (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G), QuasiIso π := by
  obtain ⟨Q, f, -, hf, hle, hQ, -, -⟩ :=
    StacksDraft.UnboundedLeftDerivedFunctor.exists_sequence_quasiIso_truncLE (IsFreeSum s)
      (fun _ _ => isFreeSum_biprod s) (exists_epi_isFreeSum s)
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G)
  have h0 := hf 0
  have hle0 : (Q 0).IsStrictlyLE 0 := hle 0
  exact ⟨Q 0, hle0, hQ 0, f 0 ≫ CochainComplex.ιTruncLE _ ((0 : ℕ) : ℤ), inferInstance⟩

end Stacks.Sites.FibredCategory.FibredCategorySituation
