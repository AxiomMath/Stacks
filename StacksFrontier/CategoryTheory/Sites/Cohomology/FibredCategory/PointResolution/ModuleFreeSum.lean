module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.CosimplicialResolutionOfModules
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.PointResolution.ModuleBasic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.PointResolution.Vanishing

/-!
# Free presheaves of modules on a fibrewise point resolution

The resolutions computing derived lower shriek at module coefficients on a fibrewise point
resolution have terms the free presheaves of `p⁻¹O`-modules on coproducts of (universe-lifted)
representable presheaves on the total category. This file defines that class, shows that it
contains zero, is closed under binary direct sums and resolves every presheaf of modules, and
proves that the complex of presheaves of `O`-modules `V ↦ G(A_{•,V})` of a member `G` has no
positive homology. This is Stacks 08Q9 for free modules, applied fibrewise: `G(A_{•,V})` is the
free simplicial `O(V)`-module on `∐_i Hom(A_{•,V}, x_i)`, whose fibres over `∐_i Hom(V, p(x_i))`
are the simplicial sets `Mor_{C_V}(A_{•,V}, h^*x_i)`, homotopy equivalent to a point.

## Main definitions

* `Stacks.Sites.FibredCategory.FibredCategorySituation.IsModuleFreeSum`: the presheaves of
  modules free on a coproduct of representables.
* `Stacks.Sites.FibredCategory.FibredCategorySituation.freeEvaluationIso`: the free presheaf of
  modules on `F`, evaluated on `A_{•,V}`, is the free simplicial `O(V)`-module on `F(A_{•,V})`.

## Main results

* `Stacks.ChaoticSite.isZero_homology_mooreComplex_of_constFibre`: for a functor `T` from sets
  to abelian groups preserving coproducts, the Moore complex of `T(S_•)` has no positive homology
  when the fibres of `S_• ⟶ K` are homotopy equivalent to a point.
* `Stacks.Sites.FibredCategory.FibredCategorySituation.exists_isModuleFreeSum_resolution`: every
  presheaf of modules has a bounded above resolution by members of the class.
* `FibredCategorySituation.isZero_modulePointMooreComplex_homology_of_isModuleFreeSum`: the
  complex `V ↦ G(A_{•,V})` of a member `G` of the class has no positive homology.

## References

* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
* [Stacks Project, Tag 08VB](https://stacks.math.columbia.edu/tag/08VB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology Simplicial

namespace Stacks.ChaoticSite

universe v

variable {S : SimplicialObject (Type v)} {K : Type v}
  (φ : S ⟶ (Functor.const SimplexCategoryᵒᵖ).obj K) (T : Type v ⥤ AddCommGrpCat.{v})
  [PreservesColimitsOfShape (Discrete K) T]

/-- The Moore complex of `T(S_•)`, for a functor `T` preserving coproducts indexed by `K`, is the
direct sum of the Moore complexes of `T` applied to the fibres of `φ : S ⟶ K`. -/
def isColimitMooreConstFibreCofan :
    IsColimit (Cofan.mk ((alternatingFaceMapComplex AddCommGrpCat.{v}).obj (S ⋙ T))
      fun k => (alternatingFaceMapComplex AddCommGrpCat.{v}).map
        (Functor.whiskerRight (constFibreι φ k) T)) := by
  refine HomologicalComplex.isColimitOfEval _ _ fun n => ?_
  exact (isColimitMapCoconeCofanMkEquiv _ _ _).symm
    (isColimitCofanMkObjOfIsColimit T _ _ (isColimitConstFibreCofan φ (op (SimplexCategory.mk n))))

/-- **The Moore complex of `T(S_•)` has no homology in a degree in which none of the Moore
complexes of `T` applied to the fibres of `φ : S ⟶ K` has any**, for a functor `T` preserving
coproducts indexed by `K`. -/
theorem isZero_homology_mooreComplex_of_constFibre_isZero (n : ℕ)
    (h : ∀ k, IsZero (((alternatingFaceMapComplex AddCommGrpCat.{v}).obj
      (constFibre φ k ⋙ T)).homology n)) :
    IsZero (((alternatingFaceMapComplex AddCommGrpCat.{v}).obj (S ⋙ T)).homology n) := by
  have := Stacks.HomologyColimit.preservesColimitsOfShape_homologyFunctor
    (A := AddCommGrpCat.{v}) (J := Discrete K) (ComplexShape.down ℕ) n
  have hc := isColimitOfPreserves
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (ComplexShape.down ℕ) n)
    (isColimitMooreConstFibreCofan φ T)
  rw [IsZero.iff_id_eq_zero]
  exact hc.hom_ext fun ⟨k⟩ => (h k).eq_of_src _ _

/-- **The Moore complex of `T(S_•)` has no homology in positive degrees when the fibres of
`φ : S ⟶ K` are homotopy equivalent to a point**, for a functor `T` preserving coproducts indexed
by `K`. -/
theorem isZero_homology_mooreComplex_of_constFibre
    (hφ : ∀ k, ∃ f : constFibre φ k ⟶ (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{v + 1},
      SimplicialObject.homotopyEquivalences (Type v) f) (n : ℕ) (hn : 0 < n) :
    IsZero (((alternatingFaceMapComplex AddCommGrpCat.{v}).obj (S ⋙ T)).homology n) :=
  isZero_homology_mooreComplex_of_constFibre_isZero φ T n fun k =>
    IsZero.of_iso (ChainComplex.alternatingConst_exactAt (T.obj PUnit.{v + 1}) n
        (Nat.pos_iff_ne_zero.mp hn)).isZero_homology
      (ModuleValued.mooreComplexHomologyIsoOfHomotopyEquiv T (hφ k).choose_spec n)

end Stacks.ChaoticSite

namespace PresheafOfModules

universe u u₁ v₁

/-- The restriction map of a free presheaf of modules sends `r · [g]` to `r|_Y · [g|_Y]`. -/
lemma freeObj_map_single {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
    (F : Cᵒᵖ ⥤ Type u) {X Y : Cᵒᵖ} (f : X ⟶ Y) (g : F.obj X) (r : R.obj X) :
    ((PresheafOfModules.freeObj (R := R) F).map f) (Finsupp.single g r) =
      Finsupp.single (F.map f g) (R.map f r) := by
  have h : (Finsupp.single g r : (PresheafOfModules.freeObj (R := R) F).obj X) =
      r • ModuleCat.freeMk g :=
    ((Finsupp.smul_single r g 1).trans (by rw [smul_eq_mul, mul_one])).symm
  have h' : (PresheafOfModules.freeObj (R := R) F).map f (ModuleCat.freeMk g) =
      ModuleCat.freeMk (F.map f g) := by
    rw [PresheafOfModules.freeObj_map]
    exact ModuleCat.freeDesc_apply _ _
  refine (congrArg ((PresheafOfModules.freeObj (R := R) F).map f) h).trans
    ((PresheafOfModules.map_smul _ f r _).trans ?_)
  rw [h']
  exact (Finsupp.smul_single _ _ _).trans (by rw [smul_eq_mul, mul_one])

end PresheafOfModules

namespace Stacks.Sites.FibredCategory.FibredCategorySituation

universe uD vD uC vC w

variable (s : FibredCategorySituation.{uD, vD, uC, vC, w})
  (O : s.base.Cᵒᵖ ⥤ RingCat.{max w uD vD uC vC})

/-- The presheaves of `p⁻¹O`-modules which are, up to isomorphism, free on a coproduct of
representables. -/
def IsModuleFreeSum : ObjectProperty (PresheafOfModules.{max w uD vD uC vC} (s.p.op ⋙ O)) :=
  fun G => ∃ (ι : Type (max w uD vD uC vC)) (x : ι → s.C),
    Nonempty ((PresheafOfModules.free.{max w uD vD uC vC} (s.p.op ⋙ O)).obj (sigmaYoneda s x) ≅ G)

/-- The free presheaf of `p⁻¹O`-modules on `sigmaYoneda` is the coproduct of the free presheaves
of modules on the lifted representables. -/
def freeSigmaYonedaModuleIso {ι : Type (max w uD vD uC vC)} (x : ι → s.C) :
    (PresheafOfModules.free.{max w uD vD uC vC} (s.p.op ⋙ O)).obj (sigmaYoneda s x) ≅
      ∐ fun i => (PresheafOfModules.free.{max w uD vD uC vC} (s.p.op ⋙ O)).obj
        (uliftYoneda.{max w uD vD uC}.obj (x i)) :=
  have := (PresheafOfModules.freeAdjunction.{max w uD vD uC vC}
    (s.p.op ⋙ O)).leftAdjoint_preservesColimits
  (isColimitCofanMkObjOfIsColimit (PresheafOfModules.free (s.p.op ⋙ O)) _ _
      (isColimitSigmaYoneda s x)).coconePointUniqueUpToIso (coproductIsCoproduct _)

/-- A free presheaf of modules on a coproduct of representables is, up to isomorphism, the
coproduct of the free presheaves of modules on the representables. -/
lemma isModuleFreeSum_iff (G : PresheafOfModules.{max w uD vD uC vC} (s.p.op ⋙ O)) :
    IsModuleFreeSum s O G ↔ ∃ (ι : Type (max w uD vD uC vC)) (x : ι → s.C),
      Nonempty ((∐ fun i => (PresheafOfModules.free.{max w uD vD uC vC} (s.p.op ⋙ O)).obj
        (uliftYoneda.{max w uD vD uC}.obj (x i))) ≅ G) :=
  ⟨fun ⟨ι, x, ⟨e⟩⟩ => ⟨ι, x, ⟨(freeSigmaYonedaModuleIso s O x).symm ≪≫ e⟩⟩,
    fun ⟨ι, x, ⟨e⟩⟩ => ⟨ι, x, ⟨freeSigmaYonedaModuleIso s O x ≪≫ e⟩⟩⟩

/-- The class of free presheaves of modules on coproducts of representables contains a zero
object: the free presheaf of modules on the empty coproduct. -/
instance containsZero_isModuleFreeSum : (IsModuleFreeSum s O).ContainsZero := by
  let x : PEmpty.{max w uD vD uC vC + 1} → s.C := fun i => nomatch i
  refine ⟨⟨(PresheafOfModules.free (s.p.op ⋙ O)).obj (sigmaYoneda s x), ?_,
    PEmpty, x, ⟨Iso.refl _⟩⟩⟩
  rw [IsZero.iff_id_eq_zero]
  ext X a
  have : IsEmpty ((sigmaYoneda s x).obj X) := ⟨fun g => nomatch g.1⟩
  exact Subsingleton.elim (α := (sigmaYoneda s x).obj X →₀ (s.p.op ⋙ O).obj X) _ _

/-- The class of free presheaves of modules on coproducts of representables is closed under
binary direct sums. -/
lemma isModuleFreeSum_biprod {F G : PresheafOfModules.{max w uD vD uC vC} (s.p.op ⋙ O)}
    (hF : IsModuleFreeSum s O F) (hG : IsModuleFreeSum s O G) : IsModuleFreeSum s O (F ⊞ G) := by
  rw [isModuleFreeSum_iff] at hF hG ⊢
  obtain ⟨ι, U, ⟨eF⟩⟩ := hF
  obtain ⟨κ, V, ⟨eG⟩⟩ := hG
  refine ⟨ι ⊕ κ, Sum.elim U V, ?_⟩
  let A' : ι → PresheafOfModules.{max w uD vD uC vC} (s.p.op ⋙ O) :=
    fun i => (PresheafOfModules.free _).obj (uliftYoneda.{max w uD vD uC}.obj (U i))
  let B' : κ → PresheafOfModules.{max w uD vD uC vC} (s.p.op ⋙ O) :=
    fun j => (PresheafOfModules.free _).obj (uliftYoneda.{max w uD vD uC}.obj (V j))
  have hAB : (fun i : ι ⊕ κ => (PresheafOfModules.free.{max w uD vD uC vC} (s.p.op ⋙ O)).obj
      (uliftYoneda.{max w uD vD uC}.obj (Sum.elim U V i))) = Sum.elim A' B' := by
    funext i
    cases i <;> rfl
  let e : Discrete.functor (fun i : ι ⊕ κ =>
      (PresheafOfModules.free.{max w uD vD uC vC} (s.p.op ⋙ O)).obj
        (uliftYoneda.{max w uD vD uC}.obj (Sum.elim U V i))) ≅
      Discrete.functor (Sum.elim A' B') :=
    NatIso.ofComponents (fun i => eqToIso (congrFun hAB i.as)) (by cat_disch)
  exact ⟨HasColimit.isoOfNatIso e ≪≫
    (coproductIsCoproduct (Sum.elim A' B')).coconePointUniqueUpToIso
      (Cofan.combPairIsColimit (coproductIsCoproduct A') (coproductIsCoproduct B')
        (coprodIsCoprod (∐ A') (∐ B'))) ≪≫
    (biprod.isoCoprod (∐ A') (∐ B')).symm ≪≫ biprod.mapIso eF eG⟩

/-- **Every presheaf of modules is a quotient of a free presheaf of modules on a coproduct of
representables**. -/
lemma exists_epi_isModuleFreeSum (G : PresheafOfModules.{max w uD vD uC vC} (s.p.op ⋙ O)) :
    ∃ (F : PresheafOfModules.{max w uD vD uC vC} (s.p.op ⋙ O)) (_ : IsModuleFreeSum s O F)
      (π : F ⟶ G), Epi π := by
  let ι : Type (max w uD vD uC vC) := Σ y : s.C, (G.obj (op y) : Type (max w uD vD uC vC))
  let x : ι → s.C := fun i => i.1
  let φ : sigmaYoneda s x ⟶ G.presheaf ⋙ forget _ :=
    { app := fun y => ↾fun g => G.map g.2.down.op g.1.2
      naturality := fun y y' f => by
        ext g
        exact G.map_comp_apply g.2.down.op f g.1.2 }
  refine ⟨_, ⟨ι, x, ⟨Iso.refl _⟩⟩, PresheafOfModules.freeObjDesc φ,
    PresheafOfModules.epi_of_surjective fun y t => ⟨ModuleCat.freeMk ⟨⟨y.unop, t⟩, ⟨𝟙 _⟩⟩, ?_⟩⟩
  refine (ModuleCat.freeDesc_apply _ _).trans ?_
  change G.map (𝟙 y.unop).op t = t
  rw [op_id, G.map_id]
  rfl

/-- **Every presheaf of modules has a resolution by free presheaves of modules on coproducts of
representables**, bounded above by `0`. -/
lemma exists_isModuleFreeSum_resolution (G : PresheafOfModules.{max w uD vD uC vC} (s.p.op ⋙ O)) :
    ∃ (Q : CochainComplex (PresheafOfModules.{max w uD vD uC vC} (s.p.op ⋙ O)) ℤ)
      (_ : Q.IsStrictlyLE 0) (_ : ∀ n, IsModuleFreeSum s O (Q.X n))
      (π : Q ⟶ (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G), QuasiIso π := by
  obtain ⟨Q, f, -, hf, hle, hQ, -, -⟩ :=
    StacksDraft.UnboundedLeftDerivedFunctor.exists_sequence_quasiIso_truncLE (IsModuleFreeSum s O)
      (fun _ _ => isModuleFreeSum_biprod s O) (exists_epi_isModuleFreeSum s O)
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G)
  exact ⟨Q 0, hle 0, hQ 0, f 0 ≫ CochainComplex.ιTruncLE _ ((0 : ℕ) : ℤ), inferInstance⟩

variable {s} {A : s.base.C ⥤ CosimplicialObject s.C}
  (hA : A ⋙ (Functor.whiskeringRight SimplexCategory s.C s.base.C).obj s.p =
    Functor.const SimplexCategory)

/-- The functor `X ↦ O(V)[X]` from sets to abelian groups. -/
abbrev freeModuleAb (V : s.base.C) : Type (max w uD vD uC vC) ⥤ AddCommGrpCat.{max w uD vD uC vC} :=
  ModuleCat.free (O.obj (op V)) ⋙ forget₂ _ AddCommGrpCat

/-- The ring isomorphism `O(V) ≅ O(p(A_{n,V}))`. -/
def pointRingEquiv (V : s.base.C) (n : SimplexCategory) :
    O.obj (op V) ≃+* O.obj (op (s.p.obj ((A.obj V).obj n))) :=
  (O.mapIso (eqToIso (obj_obj_proj s hA V n)).op).ringCatIsoToRingEquiv

variable {O} in
/-- **The free presheaf of `p⁻¹O`-modules on `F`, evaluated on `A_{•,V}`, is the free simplicial
`O(V)`-module on `F(A_{•,V})`**, as a simplicial abelian group: the coefficient rings
`O(p(A_{n,V}))` are identified with `O(V)`. -/
def freeEvaluationIso (F : s.Cᵒᵖ ⥤ Type (max w uD vD uC vC)) (V : s.base.C) :
    (A.obj V).op ⋙ ((PresheafOfModules.free (s.p.op ⋙ O)).obj F).presheaf ≅
      ((A.obj V).op ⋙ F) ⋙ freeModuleAb O V :=
  NatIso.ofComponents
    (fun n => (Finsupp.mapRange.addEquiv (pointRingEquiv O hA V n.unop).symm.toAddEquiv :
      (F.obj (op ((A.obj V).obj n.unop)) →₀ O.obj (op (s.p.obj ((A.obj V).obj n.unop)))) ≃+
        (F.obj (op ((A.obj V).obj n.unop)) →₀ O.obj (op V))).toAddCommGrpIso) (by
    intro n m θ
    refine AddCommGrpCat.hom_ext (Finsupp.addHom_ext fun g a => ?_)
    change Finsupp.mapRange (pointRingEquiv O hA V m.unop).symm (map_zero _)
        (((PresheafOfModules.freeObj (R := s.p.op ⋙ O) F).map ((A.obj V).map θ.unop).op)
          (Finsupp.single g a)) =
      Finsupp.mapDomain (F.map ((A.obj V).map θ.unop).op)
        (Finsupp.mapRange (pointRingEquiv O hA V n.unop).symm (map_zero _) (Finsupp.single g a))
    rw [PresheafOfModules.freeObj_map_single, Finsupp.mapRange_single, Finsupp.mapRange_single,
      Finsupp.mapDomain_single]
    congr 1
    obtain ⟨b, rfl⟩ := (pointRingEquiv O hA V n.unop).surjective a
    rw [RingEquiv.symm_apply_eq, RingEquiv.symm_apply_apply]
    exact ConcreteCategory.congr_hom (pointRingMap_comp_map s hA O θ.unop (op V)) b)

/-- `X ↦ O(V)[X]` preserves coproducts. -/
instance preservesColimitsOfShape_freeModuleAb (V : s.base.C) (K : Type (max w uD vD uC vC)) :
    PreservesColimitsOfShape (Discrete K) (freeModuleAb O V) :=
  have : PreservesColimitsOfSize.{max w uD vD uC vC, max w uD vD uC vC}
      (ModuleCat.free (O.obj (op V))) :=
    (ModuleCat.adj (O.obj (op V))).leftAdjoint_preservesColimits
  inferInstance

variable (hres : ∀ (V : s.base.C) (W : s.p.Fiber V),
  ∃ f : (Functor.Fiber.inducedFunctor (Functor.congr_obj hA V)).op ⋙ yoneda.obj W ⟶
      (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{vC + 1},
    SimplicialObject.homotopyEquivalences (Type vC) f)

include hres in
/-- **The simplicial abelian group `n ↦ O(V)[Hom(A_{n,V}, x)]` has no positive homology**: its
fibres over `Hom(V, p(x))` are the simplicial sets `Mor_{C_V}(A_{•,V}, h^*x)`, homotopy equivalent
to a point. -/
lemma isZero_homology_pointHomSSet_freeModuleAb (V : s.base.C) (x : s.C) (n : ℕ) (hn : 0 < n) :
    IsZero (((alternatingFaceMapComplex AddCommGrpCat.{max w uD vD uC vC}).obj
      (pointHomSSet s A V x ⋙ freeModuleAb O V)).homology n) := by
  refine Stacks.ChaoticSite.isZero_homology_mooreComplex_of_constFibre
    (pointHomSSetProj s hA V x) (freeModuleAb O V) (fun ⟨h⟩ => ?_) n hn
  obtain ⟨f₀, hf₀⟩ := hres V (pullbackFiber s h)
  let e : (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{vC + 1} ⋙
      uliftFunctor.{max w uD vD uC vC} ≅
      (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{max w uD vD uC vC + 1} :=
    Functor.constComp _ _ _ ≪≫
      (Functor.const _).mapIso (Equiv.toIso (Equiv.ulift.trans Equiv.punitEquivPUnit))
  exact ⟨(pointHomFibreIso s hA h).hom ≫ Functor.whiskerRight f₀ uliftFunctor ≫ e.hom,
    CategoryTheory.SimplicialObject.homotopyEquivalences_iso_comp_iso _ _ _
      (CategoryTheory.SimplicialObject.homotopyEquivalences_whiskering_map uliftFunctor hf₀)⟩

include hres in
/-- **For a free presheaf of modules `G` on a coproduct of representables, the complex of
presheaves of `O`-modules `V ↦ G(A_{•,V})` has no positive homology.** -/
theorem isZero_modulePointMooreComplex_homology_of_isModuleFreeSum
    (G : PresheafOfModules.{max w uD vD uC vC} (s.p.op ⋙ O)) (hG : IsModuleFreeSum s O G)
    (n : ℕ) : IsZero (((modulePointMooreComplex s hA O).obj G).homology (n + 1)) := by
  obtain ⟨ι, x, ⟨e⟩⟩ := hG
  refine IsZero.of_iso ?_ (HomologicalComplex.homologyMapIso
    ((modulePointMooreComplex s hA O).mapIso e) (n + 1)).symm
  show IsZero (HomologicalComplex.homology _ (n + 1))
  rw [← HomologicalComplex.exactAt_iff_isZero_homology, HomologicalComplex.exactAt_iff]
  refine (PresheafOfModules.toPresheaf O).reflects_exact_of_faithful _ ?_
  have h : (((PresheafOfModules.toPresheaf O).mapHomologicalComplex _).obj
      ((modulePointMooreComplex s hA O).obj
        ((PresheafOfModules.free (s.p.op ⋙ O)).obj (sigmaYoneda s x)))).ExactAt (n + 1) := by
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    refine IsZero.of_iso ?_
      (HomologicalComplex.homologyMapIso ((modulePointMooreComplexForgetIso s hA O).app _) (n + 1))
    refine isZero_pointMooreComplex_homology_of_forall s _ (n + 1) fun V => ?_
    refine IsZero.of_iso ?_ (HomologicalComplex.homologyMapIso
      ((alternatingFaceMapComplex _).mapIso (freeEvaluationIso hA (sigmaYoneda s x) V)) (n + 1))
    refine Stacks.ChaoticSite.isZero_homology_mooreComplex_of_constFibre_isZero
      (sigmaYonedaIndex s A x V) (freeModuleAb O V) (n + 1) fun i => ?_
    exact IsZero.of_iso (isZero_homology_pointHomSSet_freeModuleAb O hA hres V (x i) (n + 1)
        n.succ_pos)
      (HomologicalComplex.homologyMapIso ((alternatingFaceMapComplex _).mapIso
        (Functor.isoWhiskerRight (sigmaYonedaIndexFibreIso s A x V i) (freeModuleAb O V))) (n + 1))
  rwa [HomologicalComplex.exactAt_iff] at h

end Stacks.Sites.FibredCategory.FibredCategorySituation
