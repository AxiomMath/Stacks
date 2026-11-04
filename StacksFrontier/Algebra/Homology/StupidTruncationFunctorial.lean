module

public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import StacksFrontier.Algebra.Homology.StupidTruncation

/-!
# The stupid filtration under a map from the image of a complex by an additive functor

For an additive functor `G` and a map `ψ : G K ⟶ K'` of cochain complexes, this file
constructs the induced maps on the stupid truncations `σ^{≥q}` and on the graded pieces
`Kᵠ[-q]`, the canonical degreewise splittings of the short exact sequences
`σ^{≥q+1}K ⟶ σ^{≥q}K ⟶ Kᵠ[-q]`, and the resulting morphism from the image by `G` of the
triangle of such a sequence to the triangle for `K'`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex ComplexShape

namespace StacksDraft.StupidTruncation

noncomputable section

attribute [local instance] mono_ιStupidTrunc

section Splitting

variable {C : Type*} [Category* C] [Abelian C] (K : CochainComplex C ℤ)

open Classical in
/-- The canonical degreewise splitting of the short exact sequence
`σ^{≥p+1}K ⟶ σ^{≥p}K ⟶ Kᵖ[-p]`: in degree `p` the first term vanishes and the projection is an
isomorphism, in every other degree the first map is an isomorphism and the last term vanishes. -/
def stupidTruncGESplitting (p n : ℤ) :
    ((stupidTruncGEShortComplex K p).map (eval C (.up ℤ) n)).Splitting :=
  if hn : n = p then
    ShortComplex.Splitting.ofIsZeroOfIsIso _
      (CochainComplex.isZero_of_isStrictlyGE (K.stupidTrunc (embeddingUpIntGE (p + 1))) (p + 1)
        n (by omega))
      (by
        subst hn
        change IsIso ((stupidTruncGEπ K n).f n)
        rw [stupidTruncGEπ_f]
        infer_instance)
  else
    ShortComplex.Splitting.ofIsIsoOfIsZero _
      (by
        change IsIso ((stupidTruncGEMapLE K (show p ≤ p + 1 by omega)).f n)
        by_cases hpn : p < n
        · rw [stupidTruncGEMapLE_f K _ n (by omega)]
          infer_instance
        · exact IsZero.isIso
            (CochainComplex.isZero_of_isStrictlyGE
              (K.stupidTrunc (embeddingUpIntGE (p + 1))) (p + 1) n (by omega))
            (CochainComplex.isZero_of_isStrictlyGE
              (K.stupidTrunc (embeddingUpIntGE p)) p n (by omega)) _)
      (isZero_single_obj_X (.up ℤ) p (K.X p) n hn)

/-- In degree `p` the section of the canonical splitting inverts the projection. -/
theorem stupidTruncGESplitting_s_self (p : ℤ) :
    (stupidTruncGESplitting K p p).s =
      @inv _ _ _ _ ((stupidTruncGEπ K p).f p) (by
        rw [stupidTruncGEπ_f]
        infer_instance) := by
  simp only [stupidTruncGESplitting, dite_eq_left rfl, ShortComplex.Splitting.ofIsZeroOfIsIso]
  rfl

/-- Away from degree `p` the section of the canonical splitting vanishes. -/
theorem stupidTruncGESplitting_s_of_ne (p n : ℤ) (hn : n ≠ p) :
    (stupidTruncGESplitting K p n).s = 0 := by
  simp only [stupidTruncGESplitting, dite_eq_right hn, ShortComplex.Splitting.ofIsIsoOfIsZero]

/-- In degree `p` the retraction of the canonical splitting vanishes. -/
theorem stupidTruncGESplitting_r_self (p : ℤ) :
    (stupidTruncGESplitting K p p).r = 0 := by
  simp only [stupidTruncGESplitting, dite_eq_left rfl, ShortComplex.Splitting.ofIsZeroOfIsIso]

end Splitting

section DegreewiseSplit

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  (G : C ⥤ D) [G.Additive]

/-- **The connecting morphism of degreewise split sequences is natural** with respect to maps
from the image of one sequence by an additive functor to another, compatible with the sections
and the retractions of the splittings. -/
theorem mapHomologicalComplex_homOfDegreewiseSplit_comp
    (S₁ : ShortComplex (CochainComplex C ℤ)) (σ₁ : ∀ n, (S₁.map (eval C (.up ℤ) n)).Splitting)
    (S₂ : ShortComplex (CochainComplex D ℤ)) (σ₂ : ∀ n, (S₂.map (eval D (.up ℤ) n)).Splitting)
    (ρ₁ : (G.mapHomologicalComplex (.up ℤ)).obj S₁.X₁ ⟶ S₂.X₁)
    (ρ₂ : (G.mapHomologicalComplex (.up ℤ)).obj S₁.X₂ ⟶ S₂.X₂)
    (ρ₃ : (G.mapHomologicalComplex (.up ℤ)).obj S₁.X₃ ⟶ S₂.X₃)
    (hs : ∀ n, G.map (σ₁ n).s ≫ ρ₂.f n = ρ₃.f n ≫ (σ₂ n).s)
    (hr : ∀ n, G.map (σ₁ n).r ≫ ρ₁.f n = ρ₂.f n ≫ (σ₂ n).r) :
    ((G.mapHomologicalComplex (.up ℤ)).map (CochainComplex.homOfDegreewiseSplit S₁ σ₁) ≫
        ((G.mapHomologicalComplex (.up ℤ)).commShiftIso (1 : ℤ)).hom.app S₁.X₁) ≫
        ρ₁⟦(1 : ℤ)⟧' =
      ρ₃ ≫ CochainComplex.homOfDegreewiseSplit S₂ σ₂ := by
  ext n
  have e₁ : (CochainComplex.homOfDegreewiseSplit S₁ σ₁).f n =
      (σ₁ n).s ≫ S₁.X₂.d n (n + 1) ≫ (σ₁ (n + 1)).r := by
    rw [CochainComplex.homOfDegreewiseSplit_f]
    rfl
  have e₂ : (CochainComplex.homOfDegreewiseSplit S₂ σ₂).f n =
      (σ₂ n).s ≫ S₂.X₂.d n (n + 1) ≫ (σ₂ (n + 1)).r := by
    rw [CochainComplex.homOfDegreewiseSplit_f]
    rfl
  have hc : G.map (S₁.X₂.d n (n + 1)) ≫ ρ₂.f (n + 1) = ρ₂.f n ≫ S₂.X₂.d n (n + 1) :=
    (ρ₂.comm n (n + 1)).symm
  show (G.map ((CochainComplex.homOfDegreewiseSplit S₁ σ₁).f n) ≫ 𝟙 _) ≫ ρ₁.f (n + 1) =
    ρ₃.f n ≫ (CochainComplex.homOfDegreewiseSplit S₂ σ₂).f n
  rw [e₁, e₂, Category.comp_id, G.map_comp, G.map_comp, Category.assoc, Category.assoc, hr,
    reassoc_of% hc, reassoc_of% (hs n)]

end DegreewiseSplit

section Comparison

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D] (G : C ⥤ D)
  [G.Additive] {K : CochainComplex C ℤ} {K' : CochainComplex D ℤ}
  (ψ : (G.mapHomologicalComplex (.up ℤ)).obj K ⟶ K')

/-- The map `G(σ^{≥q}K) ⟶ σ^{≥q}K'` induced on stupid truncations by a map `G K ⟶ K'`. -/
def stupidTruncGELift (q : ℤ) :
    (G.mapHomologicalComplex (.up ℤ)).obj (K.stupidTrunc (embeddingUpIntGE q)) ⟶
      K'.stupidTrunc (embeddingUpIntGE q) :=
  liftStupidTrunc K' (embeddingUpIntGE q)
    ((G.mapHomologicalComplex (.up ℤ)).map (ιStupidTrunc K (embeddingUpIntGE q)) ≫ ψ)

/-- The induced map on stupid truncations is compatible with the inclusions. -/
@[reassoc]
theorem stupidTruncGELift_ι (q : ℤ) :
    stupidTruncGELift G ψ q ≫ ιStupidTrunc K' (embeddingUpIntGE q) =
      (G.mapHomologicalComplex (.up ℤ)).map (ιStupidTrunc K (embeddingUpIntGE q)) ≫ ψ :=
  liftStupidTrunc_ι _ _ _

/-- The induced maps on stupid truncations are compatible with the comparisons of the tower. -/
theorem map_stupidTruncGEMapLE_comp_stupidTruncGELift {a b : ℤ} (h : a ≤ b) :
    (G.mapHomologicalComplex (.up ℤ)).map (stupidTruncGEMapLE K h) ≫ stupidTruncGELift G ψ a =
      stupidTruncGELift G ψ b ≫ stupidTruncGEMapLE K' h := by
  apply (cancel_mono (ιStupidTrunc K' (embeddingUpIntGE a))).1
  rw [Category.assoc, Category.assoc, stupidTruncGELift_ι, stupidTruncGEMapLE_ι,
    stupidTruncGELift_ι, ← Functor.map_comp_assoc, stupidTruncGEMapLE_ι]

/-- The map `G(Kᵖ[-p]) ⟶ K'ᵖ[-p]` induced on the graded pieces of the stupid filtrations. -/
def stupidTruncGEGradedMap (p : ℤ) :
    (G.mapHomologicalComplex (.up ℤ)).obj ((single C (.up ℤ) p).obj (K.X p)) ⟶
      (single D (.up ℤ) p).obj (K'.X p) :=
  (singleMapHomologicalComplex G (.up ℤ) p).hom.app (K.X p) ≫ (single D (.up ℤ) p).map (ψ.f p)

/-- The induced maps on stupid truncations and on graded pieces are compatible with the
projections. -/
theorem stupidTruncGELift_comp_stupidTruncGEπ (p : ℤ) :
    stupidTruncGELift G ψ p ≫ stupidTruncGEπ K' p =
      (G.mapHomologicalComplex (.up ℤ)).map (stupidTruncGEπ K
          p) ≫ stupidTruncGEGradedMap G ψ p := by
  apply to_single_hom_ext
  have h := congrArg (fun φ => φ.f p) (stupidTruncGELift_ι G ψ p)
  dsimp only [HomologicalComplex.comp_f] at h
  rw [ιStupidTruncGE_f K' p p le_rfl] at h
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, stupidTruncGEπ_f, reassoc_of% h,
    stupidTruncGEGradedMap, HomologicalComplex.comp_f, singleMapHomologicalComplex_hom_app_self,
    single_map_f_self, Functor.mapHomologicalComplex_map_f, Functor.mapHomologicalComplex_map_f,
    stupidTruncGEπ_f, ιStupidTruncGE_f K p p le_rfl]
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc, ← G.map_comp_assoc,
    Iso.inv_hom_id, G.map_id, Category.id_comp]

/-- **The connecting morphisms of the stupid filtrations are compatible** with the maps induced
by `ψ : G K ⟶ K'` on truncations and on graded pieces: the square involving the connecting
morphisms `Kᵖ[-p] ⟶ σ^{≥p+1}K[1]` of the canonical splittings commutes. -/
theorem stupidTruncGE_homOfDegreewiseSplit_comp (p : ℤ) :
    ((G.mapHomologicalComplex (.up ℤ)).map (CochainComplex.homOfDegreewiseSplit
        (stupidTruncGEShortComplex K p) (stupidTruncGESplitting K p)) ≫
        ((G.mapHomologicalComplex (.up ℤ)).commShiftIso (1 : ℤ)).hom.app _) ≫
        (stupidTruncGELift G ψ (p + 1))⟦(1 : ℤ)⟧' =
      stupidTruncGEGradedMap G ψ p ≫ CochainComplex.homOfDegreewiseSplit
        (stupidTruncGEShortComplex K' p) (stupidTruncGESplitting K' p) := by
  refine mapHomologicalComplex_homOfDegreewiseSplit_comp G (stupidTruncGEShortComplex K p)
    (stupidTruncGESplitting K p) (stupidTruncGEShortComplex K' p) (stupidTruncGESplitting K' p)
    (stupidTruncGELift G ψ (p + 1)) (stupidTruncGELift G ψ p) (stupidTruncGEGradedMap G ψ p)
    (fun n => ?_) (fun n => ?_)
  · by_cases hn : n = p
    · subst hn
      have hπ := congrArg (fun φ => φ.f n) (stupidTruncGELift_comp_stupidTruncGEπ G ψ n)
      dsimp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f] at hπ
      have hs := (stupidTruncGESplitting K n n).s_g
      have hs' := (stupidTruncGESplitting K' n n).s_g
      have : Mono ((stupidTruncGEπ K' n).f n) := by
        rw [stupidTruncGEπ_f]
        infer_instance
      refine (cancel_mono ((stupidTruncGEπ K' n).f n)).1 ?_
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (G.map (stupidTruncGESplitting K n n).s ≫ ·) hπ).trans ?_
      refine (Category.assoc _ _ _).symm.trans ?_
      refine (congrArg (· ≫ (stupidTruncGEGradedMap G ψ n).f n) ((G.map_comp _ _).symm.trans
        ((congrArg G.map hs).trans (G.map_id _)))).trans ?_
      refine (Category.id_comp _).trans ?_
      refine (Category.comp_id _).symm.trans ?_
      refine (congrArg ((stupidTruncGEGradedMap G ψ n).f n ≫ ·) hs'.symm).trans ?_
      exact (Category.assoc _ _ _).symm
    · exact (Functor.map_isZero G (isZero_single_obj_X (.up ℤ) p (K.X p) n hn)).eq_of_src _ _
  · by_cases hn : n = p
    · subst hn
      rw [stupidTruncGESplitting_r_self, stupidTruncGESplitting_r_self, G.map_zero, zero_comp,
        comp_zero]
    · have hle := congrArg (fun φ => φ.f n)
        (map_stupidTruncGEMapLE_comp_stupidTruncGELift G ψ (show p ≤ p + 1 by omega))
      dsimp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f] at hle
      have hr' := (stupidTruncGESplitting K' p n).f_r
      have hrf := (stupidTruncGESplitting K p n).r_f
      rw [stupidTruncGESplitting_s_of_ne K p n hn, comp_zero, sub_zero] at hrf
      refine (Category.comp_id _).symm.trans ?_
      refine (congrArg (_ ≫ ·) hr'.symm).trans ?_
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (G.map (stupidTruncGESplitting K p n).r ≫ ·)
        (Category.assoc _ _ _).symm).trans ?_
      refine (congrArg (fun t => G.map (stupidTruncGESplitting K p n).r ≫ t ≫ _)
        hle.symm).trans ?_
      refine (congrArg (G.map (stupidTruncGESplitting K p n).r ≫ ·)
        (Category.assoc _ _ _)).trans ?_
      refine (Category.assoc _ _ _).symm.trans ?_
      refine (congrArg (· ≫ _) ((G.map_comp _ _).symm.trans
        ((congrArg G.map hrf).trans (G.map_id _)))).trans ?_
      exact Category.id_comp _

/-- **The morphism of triangles of stupid filtrations** induced by `ψ : G K ⟶ K'`, from the image
by `G` of the triangle `σ^{≥p+1}K ⟶ σ^{≥p}K ⟶ Kᵖ[-p] ⟶ σ^{≥p+1}K[1]` of the canonical splitting
to the corresponding triangle of `K'`. -/
def stupidTruncGETriangleHom (p : ℤ) :
    (G.mapHomologicalComplex (.up ℤ)).mapTriangle.obj (CochainComplex.triangleOfDegreewiseSplit
        (stupidTruncGEShortComplex K p) (stupidTruncGESplitting K p)) ⟶
      CochainComplex.triangleOfDegreewiseSplit (stupidTruncGEShortComplex K' p)
        (stupidTruncGESplitting K' p) :=
  Pretriangulated.Triangle.homMk _ _ (stupidTruncGELift G ψ (p + 1)) (stupidTruncGELift G ψ p)
    (stupidTruncGEGradedMap G ψ p)
    (map_stupidTruncGEMapLE_comp_stupidTruncGELift G ψ (show p ≤ p + 1 by omega))
    (stupidTruncGELift_comp_stupidTruncGEπ G ψ p).symm
    (stupidTruncGE_homOfDegreewiseSplit_comp G ψ p)

end Comparison

section Single

variable {𝒜 ℬ 𝒜' ℬ' : Type*} [Category* 𝒜] [Category* ℬ] [Category* 𝒜'] [Category* ℬ']
  [Preadditive 𝒜] [Preadditive ℬ] [Preadditive 𝒜'] [Preadditive ℬ'] [HasZeroObject 𝒜]
  [HasZeroObject ℬ] [HasZeroObject 𝒜'] [HasZeroObject ℬ'] (I : 𝒜 ⥤ ℬ) (I' : 𝒜' ⥤ ℬ')
  (Gb : ℬ ⥤ ℬ') (Ga : 𝒜 ⥤ 𝒜') [I.Additive] [I'.Additive] [Gb.Additive] [Ga.Additive]
  (τ : I ⋙ Gb ⟶ Ga ⋙ I')

/-- Maps of objects placed in degree `p`, transported along a square of additive functors with a
natural transformation `τ : I ⋙ Gb ⟶ Ga ⋙ I'`: a degree-`p` identity
`Gb u ≫ τ_M ≫ I' φ' = φ ≫ u'` gives the corresponding identity of maps of single complexes. -/
theorem mapHomologicalComplex_single_comp_eq {N : ℬ} {N' : ℬ'} {M : 𝒜} {M' : 𝒜'}
    (u : N ⟶ I.obj M) (u' : N' ⟶ I'.obj M') (φ : Gb.obj N ⟶ N') (φ' : Ga.obj M ⟶ M')
    (h : Gb.map u ≫ τ.app M ≫ I'.map φ' = φ ≫ u') (p : ℤ) :
    (Gb.mapHomologicalComplex (.up ℤ)).map ((single ℬ (.up ℤ) p).map u ≫
        (singleMapHomologicalComplex I (.up ℤ) p).inv.app M) ≫
      ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app ((single 𝒜 (.up ℤ) p).obj M) ≫
        (I'.mapHomologicalComplex (.up ℤ)).map
          ((singleMapHomologicalComplex Ga (.up ℤ) p).hom.app M ≫ (single 𝒜' (.up ℤ) p).map φ')) =
      ((singleMapHomologicalComplex Gb (.up ℤ) p).hom.app N ≫ (single ℬ' (.up ℤ) p).map φ) ≫
        ((single ℬ' (.up ℤ) p).map u' ≫ (singleMapHomologicalComplex I' (.up ℤ) p).inv.app M') := by
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  by_cases hi : i = p
  · subst hi
    have hτ := τ.naturality (singleObjXSelf (.up ℤ) i M).inv
    dsimp only [Functor.comp_map] at hτ
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      NatTrans.mapHomologicalComplex_app_f, single_map_f_self,
      singleMapHomologicalComplex_hom_app_self, singleMapHomologicalComplex_inv_app_self,
      Functor.map_comp, Category.assoc]
    simp only [Iso.inv_hom_id_assoc]
    rw [← Gb.map_comp_assoc (singleObjXSelf (.up ℤ) i (I.obj M)).inv, Iso.inv_hom_id, Gb.map_id,
      Category.id_comp, reassoc_of% hτ, ← I'.map_comp_assoc (Ga.map (singleObjXSelf (.up ℤ) i
          M).inv),
      ← Ga.map_comp, Iso.inv_hom_id, Ga.map_id, I'.map_id, Category.id_comp,
      ← I'.map_comp_assoc, Iso.inv_hom_id, I'.map_id, Category.id_comp, reassoc_of% h]
  · exact (Functor.map_isZero Gb (isZero_single_obj_X (.up ℤ) p N i hi)).eq_of_src _ _

/-- `mapHomologicalComplex_single_comp_eq` for isomorphisms `u` and `u'`, with the
identifications of single complexes written as isomorphisms. -/
theorem mapHomologicalComplex_single_comp_eq_iso {N : ℬ} {N' : ℬ'} {M : 𝒜} {M' : 𝒜'}
    (u : N ≅ I.obj M) (u' : N' ≅ I'.obj M') (φ : Gb.obj N ⟶ N') (φ' : Ga.obj M ⟶ M')
    (h : Gb.map u.hom ≫ τ.app M ≫ I'.map φ' = φ ≫ u'.hom) (p : ℤ) :
    (Gb.mapHomologicalComplex (.up ℤ)).map ((single ℬ (.up ℤ) p).mapIso u ≪≫
        ((singleMapHomologicalComplex I (.up ℤ) p).app M).symm).hom ≫
      ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app ((single 𝒜 (.up ℤ) p).obj M) ≫
        (I'.mapHomologicalComplex (.up ℤ)).map
          ((singleMapHomologicalComplex Ga (.up ℤ) p).hom.app M ≫ (single 𝒜' (.up ℤ) p).map φ')) =
      ((singleMapHomologicalComplex Gb (.up ℤ) p).hom.app N ≫ (single ℬ' (.up ℤ) p).map φ) ≫
        ((single ℬ' (.up ℤ) p).mapIso u' ≪≫
          ((singleMapHomologicalComplex I' (.up ℤ) p).app M').symm).hom :=
  mapHomologicalComplex_single_comp_eq I I' Gb Ga τ u.hom u'.hom φ φ' h p

end Single

end

end StacksDraft.StupidTruncation
