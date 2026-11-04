module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CechResolutionGood07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrisDirectImageEval07Q9

/-!
# The Čech pullback along a morphism of systems of thickenings

Let `f : X/S ⟶ X'/S'` be a morphism of global crystalline situations (source `S`, target `S'`),
let `T'` be a cosimplicial system of thickenings of `Cris(X'/S')` (indexed `(n, e)`, as in
`...SmallSite.sectionsComplex`), let `T` be one of `Cris(X/S)`, and let a shift `k` and morphisms

`τ n e : f(T(n)_e) ⟶ T'(n)_{e + k}`

of `CRIS(X'/S')` be given, natural in both indices.  For an abelian sheaf `G` on `Cris(X/S)`
this file builds the map of Čech complexes

`M_{T'}(f_{cris, *}G) ⟶ M_T(G)`,  `(lim_e (f_{cris, *}G)(T'(n)_e))_n ⟶ (lim_e G(T(n)_e))_n`,

degreewise the limit of the evaluations `...SmallSite.crisDirectImageEval` at the `τ n e`.  It
is natural in `G`.  This is the pullback map of [Stacks, Tag 07Q9] on Čech complexes, before
the identification of `M_T(G)` with the complex of the source crystal.

## References

* [Stacks Project, Lemma 60.26.3, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
* [Stacks Project, Proposition 60.20.1, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S S' : GlobalCrystallineSituation.{u}} {fS : S.S ⟶ S'.S} {fX : S.X ⟶ S'.X}
  {hf : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap fS = fX ≫ S'.toClosedFiber}

/-- **A morphism of systems of thickenings over `f`, with a level shift.**  For every `n` and `e`
a morphism `f(T(n)_e) ⟶ T'(n)_{e + k}` of `CRIS(X'/S')` out of the image of `T(n)_e` under change
of divided power base, natural in the simplicial and in the level direction. -/
structure CechSystemHom (fS : S.S ⟶ S'.S) (fX : S.X ⟶ S'.X)
    (hf : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap fS = fX ≫ S'.toClosedFiber)
    (T : SimplicialObject (ℕ ⥤ CrystallineThickening S))
    (T' : SimplicialObject (ℕ ⥤ CrystallineThickening S')) where
  /-- The level shift. -/
  k : ℕ
  /-- The morphisms. -/
  τ (n : SimplexCategory) (e : ℕ) :
    (changeBase S S' fS fX hf).obj ((CrystallineThickening.ι S).obj ((T.obj (op n)).obj e)) ⟶
      (CrystallineThickening.ι S').obj ((T'.obj (op n)).obj (e + k))
  /-- Naturality in the level. -/
  naturality_level (n : SimplexCategory) {e e' : ℕ} (h : e ⟶ e') :
    (changeBase S S' fS fX hf).map ((CrystallineThickening.ι S).map ((T.obj (op n)).map h)) ≫
        τ n e' =
      τ n e ≫ (CrystallineThickening.ι S').map ((T'.obj (op n)).map (homOfLE (by
        have := leOfHom h; omega)))
  /-- Naturality in the simplicial direction. -/
  naturality_simplicial {m n : SimplexCategory} (φ : m ⟶ n) (e : ℕ) :
    (changeBase S S' fS fX hf).map ((CrystallineThickening.ι S).map ((T.map φ.op).app e)) ≫
        τ m e =
      τ n e ≫ (CrystallineThickening.ι S').map ((T'.map φ.op).app (e + k))

namespace CechSystemHom

variable {T : SimplicialObject (ℕ ⥤ CrystallineThickening S)}
  {T' : SimplicialObject (ℕ ⥤ CrystallineThickening S')} (Φ : CechSystemHom fS fX hf T T')

/-- **The Čech pullback in one cosimplicial degree**:
`lim_e (f_{cris, *}G)(T'(n)_e) ⟶ lim_e G(T(n)_e)`, whose `e`-th component is the projection to
the level `e + k` followed by the evaluation at `τ n e`. -/
def app (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) (n : SimplexCategory) :
    (cosimplicialSections T' ((crisDirectImage S S' fS fX hf).obj G).obj).obj n ⟶
      (cosimplicialSections T G.obj).obj n :=
  limit.lift ((sectionSystem T G.obj).obj n)
    { pt := (cosimplicialSections T' ((crisDirectImage S S' fS fX hf).obj G).obj).obj n
      π :=
        { app := fun e => limit.π
              ((sectionSystem T' ((crisDirectImage S S' fS fX hf).obj G).obj).obj n)
              (op (e.unop + Φ.k)) ≫ crisDirectImageEval S S' fS fX hf (Φ.τ n e.unop) G
          naturality := by
            intro e e' h
            have hle : e'.unop + Φ.k ≤ e.unop + Φ.k := Nat.add_le_add_right (leOfHom h.unop) _
            have hcomp := crisDirectImageEval_comp S S' fS fX hf ((T.obj (op n)).map h.unop)
              ((T'.obj (op n)).map (homOfLE hle)) (Φ.τ n e'.unop) (Φ.τ n e.unop)
              (Φ.naturality_level n h.unop) G
            have hw := limit.w
              ((sectionSystem T' ((crisDirectImage S S' fS fX hf).obj G).obj).obj n)
              (homOfLE hle).op
            exact (Category.id_comp _).trans <| (congrArg (· ≫ _) hw.symm).trans
              ((Category.assoc _ _ _).trans
                ((congrArg (_ ≫ ·) hcomp).trans (Category.assoc _ _ _).symm)) } }

/-- The components of `app`. -/
@[reassoc (attr := simp)]
theorem app_π (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) (n : SimplexCategory)
    (e : ℕ) :
    Φ.app G n ≫ limit.π ((sectionSystem T G.obj).obj n) (op e) =
      limit.π ((sectionSystem T' ((crisDirectImage S S' fS fX hf).obj G).obj).obj n)
          (op (e + Φ.k)) ≫ crisDirectImageEval S S' fS fX hf (Φ.τ n e) G :=
  limit.lift_π _ _

/-- **The Čech pullback as a morphism of cosimplicial abelian groups.** -/
def cosimplicialMap (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) :
    cosimplicialSections T' ((crisDirectImage S S' fS fX hf).obj G).obj ⟶
      cosimplicialSections T G.obj where
  app n := Φ.app G n
  naturality {n m} φ := by
    refine limit.hom_ext fun e => ?_
    have hcomp := crisDirectImageEval_comp S S' fS fX hf ((T.map φ.op).app e.unop)
      ((T'.map φ.op).app (e.unop + Φ.k)) (Φ.τ m e.unop) (Φ.τ n e.unop)
      (Φ.naturality_simplicial φ e.unop) G
    have h1 := Φ.app_π G m e.unop
    have h2 := Φ.app_π G n e.unop
    have h3 := limMap_π ((sectionSystem T' ((crisDirectImage S S' fS fX hf).obj G).obj).map φ)
      (op (e.unop + Φ.k))
    have h4 := limMap_π ((sectionSystem T G.obj).map φ) e
    refine ((Category.assoc _ _ _).trans ?_).trans (Category.assoc _ _ _).symm
    refine ((congrArg (_ ≫ ·) h1).trans ?_).trans (congrArg (_ ≫ ·) h4).symm
    refine ((Category.assoc _ _ _).symm.trans ?_).trans (Category.assoc _ _ _)
    refine ((congrArg (· ≫ _) h3).trans ?_).trans (congrArg (· ≫ _) h2).symm
    refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hcomp).trans ?_)
    exact (Category.assoc _ _ _).symm

/-- **The Čech pullback is natural in the sheaf.** -/
@[reassoc]
theorem cosimplicialMap_naturality {G H : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}}
    (ψ : G ⟶ H) :
    (cosimplicialSectionsFunctor T').map ((crisDirectImage S S' fS fX hf).map ψ).hom ≫
        Φ.cosimplicialMap H =
      Φ.cosimplicialMap G ≫ (cosimplicialSectionsFunctor T).map ψ.hom := by
  refine NatTrans.ext (funext fun n => ?_)
  refine limit.hom_ext (F := (sectionSystem T H.obj).obj n) fun e => ?_
  have hnat := crisDirectImageEval_naturality S S' fS fX hf (Φ.τ n e.unop) ψ
  have h1 := levelLimitFunctor_map_π (T'.obj (op n)) ((crisDirectImage S S' fS fX hf).map ψ).hom
    (op (e.unop + Φ.k))
  have h2 := levelLimitFunctor_map_π (T.obj (op n)) ψ.hom e
  have h3 := Φ.app_π H n e.unop
  have h4 := Φ.app_π G n e.unop
  show ((levelLimitFunctor (T'.obj (op n))).map ((crisDirectImage S S' fS fX hf).map ψ).hom ≫
      Φ.app H n) ≫ _ = (Φ.app G n ≫ (levelLimitFunctor (T.obj (op n))).map ψ.hom) ≫ _
  refine ((Category.assoc _ _ _).trans ?_).trans (Category.assoc _ _ _).symm
  erw [h3, h2, reassoc_of% h1, reassoc_of% h4]
  exact congrArg (_ ≫ ·) hnat

/-- **The Čech pullback on complexes of sheaves**: for a complex `K` of abelian sheaves on
`Cris(X/S)`, the map of complexes of cosimplicial groups
`Č_{T'}(f_{cris, *}K) ⟶ Č_T(K)`, degreewise `cosimplicialMap`. -/
def cechMap (K : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℕ) :
    (cechCosimplicialComplex T').obj
        (((crisDirectImage S S' fS fX hf).mapHomologicalComplex _).obj K) ⟶
      (cechCosimplicialComplex T).obj K where
  f a := Φ.cosimplicialMap (K.X a)
  comm' a b _ := (Φ.cosimplicialMap_naturality (K.d a b)).symm

/-- **The Čech pullback on the Čech double complexes.** -/
def cechDoubleMap (K : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℕ) :
    (cechDoubleComplex T').obj
        (((crisDirectImage S S' fS fX hf).mapHomologicalComplex _).obj K) ⟶
      (cechDoubleComplex T).obj K :=
  (cosimplicialDoubleComplexFunctor ⋙ HomologicalComplex₂.flipFunctor _ _ _).map (Φ.cechMap K)

end CechSystemHom

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
