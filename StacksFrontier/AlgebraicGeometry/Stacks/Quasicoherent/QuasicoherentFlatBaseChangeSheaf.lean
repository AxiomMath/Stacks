module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CoheratorSheaf
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentPullback
public import StacksFrontier.CategoryTheory.Sites.Localization.Relocalize
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BigSmallEtaleComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentFlatBaseChangeSheafFppf
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafifiedPullbackComparisonTranspose

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v w u₁ v₁ u₂ v₂

namespace Stacks.PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}}

/-- **Restriction along isomorphic functors.**  For functors `q₁ ≅ q₂ : C ⥤ D`, a presheaf of
modules `M` on `D` restricted along `q₂` and along `q₁`, with the scalars moved to a common
presheaf of rings `S` by maps `σ₂`, `σ₁` that the isomorphism matches, gives isomorphic presheaves
of `S`-modules; on sections the isomorphism is restriction of `M` along the components of the
isomorphism of functors. -/
def restrictScalarsPushforward₀Iso (M : PresheafOfModules.{v} R) {q₁ q₂ : C ⥤ D} (θ : q₁ ≅ q₂)
    (σ₁ : S ⟶ q₁.op ⋙ R) (σ₂ : S ⟶ q₂.op ⋙ R)
    (hσ : ∀ (c : Cᵒᵖ) (r : S.obj c),
      (R.map (θ.hom.app c.unop).op).hom ((σ₂.app c).hom r) = (σ₁.app c).hom r) :
    (PresheafOfModules.pushforward σ₂).obj M ≅ (PresheafOfModules.pushforward σ₁).obj M :=
  _root_.PresheafOfModules.isoOfForgetIso
    (Functor.isoWhiskerRight (NatIso.op θ) (M.presheaf ⋙ forget AddCommGrpCat))
    (fun c m => M.map (θ.hom.app c.unop).op m) (fun _ _ => rfl)
    (fun _ _ _ => map_add (M.map _).hom _ _)
    (fun c r m => by
      let m' : M.obj (Opposite.op (q₂.obj c.unop)) := m
      have h₁ : r • m = (σ₂.app c).hom r • m' := rfl
      rw [h₁]
      refine (M.map_smul (θ.hom.app c.unop).op ((σ₂.app c).hom r) m').trans ?_
      rw [hσ]
      rfl)

/-- On sections over `c`, the isomorphism `restrictScalarsPushforward₀Iso` is the restriction map
of `M` along the component of `θ` at `c`. -/
theorem restrictScalarsPushforward₀Iso_hom_app_apply (M : PresheafOfModules.{v} R)
    {q₁ q₂ : C ⥤ D} (θ : q₁ ≅ q₂) (σ₁ : S ⟶ q₁.op ⋙ R) (σ₂ : S ⟶ q₂.op ⋙ R)
    (hσ : ∀ (c : Cᵒᵖ) (r : S.obj c),
      (R.map (θ.hom.app c.unop).op).hom ((σ₂.app c).hom r) = (σ₁.app c).hom r)
    (c : Cᵒᵖ) (m : M.obj (Opposite.op (q₂.obj c.unop))) :
    (restrictScalarsPushforward₀Iso M θ σ₁ σ₂ hσ).hom.app c m =
      M.map (θ.hom.app c.unop).op m := by
  rfl

end Stacks.PresheafOfModules

namespace Stacks.CategoryTheory.Equivalence

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- Two equivalences with isomorphic functors have isomorphic inverses, by the unit of the
second and the counit of the first. -/
def inverseIsoOfFunctorIso (e e' : C ≌ D) (i : e'.functor ≅ e.functor) :
    e'.inverse ≅ e.inverse :=
  (Functor.rightUnitor _).symm ≪≫ Functor.isoWhiskerLeft e'.inverse e.unitIso ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft e'.inverse i.symm ≪≫ e'.counitIso)
      e.inverse ≪≫ Functor.leftUnitor _

/-- The isomorphism of inverses of `inverseIsoOfFunctorIso` lies over the two counits. -/
theorem functor_map_inverseIsoOfFunctorIso_hom_app_comp_counit (e e' : C ≌ D)
    (i : e'.functor ≅ e.functor) (T : D) :
    e.functor.map ((inverseIsoOfFunctorIso e e' i).hom.app T) ≫ e.counit.app T =
      i.inv.app _ ≫ e'.counit.app T := by
  have h1 := e.counit_naturality (i.inv.app (e'.inverse.obj T) ≫ e'.counit.app T)
  have h2 := e.functor_unit_comp (e'.inverse.obj T)
  simp only [Functor.comp_obj, Functor.id_obj] at h1 h2
  show e.functor.map (𝟙 _ ≫ e.unit.app _ ≫ 𝟙 _ ≫
      e.inverse.map (i.inv.app _ ≫ e'.counit.app T) ≫ 𝟙 _) ≫ e.counit.app T = _
  rw [Category.id_comp, Category.id_comp, Category.comp_id, Functor.map_comp, Category.assoc, h1,
    ← Category.assoc, h2]
  exact Category.id_comp _

variable {C' : Type*} [Category* C']

/-- A functor `G` into the source of an equivalence `e` whose composite with `e.functor` is
isomorphic to `H` is isomorphic to `H ⋙ e.inverse`, by the unit of `e`. -/
def isoCompInverseOfIso (e : C ≌ D) {G : C' ⥤ C} {H : C' ⥤ D} (α : G ⋙ e.functor ≅ H) :
    G ≅ H ⋙ e.inverse :=
  (Functor.rightUnitor _).symm ≪≫ Functor.isoWhiskerLeft G e.unitIso ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight α e.inverse

/-- The isomorphism of `isoCompInverseOfIso` lies over `α` and the counit of `e`. -/
theorem functor_map_isoCompInverseOfIso_hom_app_comp_counit (e : C ≌ D) {G : C' ⥤ C}
    {H : C' ⥤ D} (α : G ⋙ e.functor ≅ H) (c : C') :
    e.functor.map ((isoCompInverseOfIso e α).hom.app c) ≫ e.counit.app (H.obj c) =
      α.hom.app c := by
  have h1 := e.counit_naturality (α.hom.app c)
  have h2 := e.functor_unit_comp (G.obj c)
  simp only [Functor.comp_obj, Functor.id_obj] at h1 h2
  show e.functor.map (𝟙 _ ≫ e.unit.app _ ≫ 𝟙 _ ≫ e.inverse.map (α.hom.app c)) ≫
    e.counit.app (H.obj c) = _
  rw [Category.id_comp, Category.id_comp, Functor.map_comp, Category.assoc, h1,
    ← Category.assoc, h2]
  exact Category.id_comp _

end Stacks.CategoryTheory.Equivalence

namespace Stacks.CategoryTheory.Adjunction

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- **A transpose through the unit of a second left adjoint is invertible.**  Let `L` and `L'`
be two left adjoints of the same functor `R`.  If `t : M ⟶ R N` is an isomorphism `M ≅ M'`
followed by the unit of `L' ⊣ R` at `M'` and the image under `R` of an isomorphism
`L' M' ≅ N`, then the transpose of `t` along `L ⊣ R` is an isomorphism: it is `L` of the first
isomorphism, the comparison `L ≅ L'` of the two left adjoints at `M'`, and the second
isomorphism. -/
theorem isIso_homEquiv_symm_of_eq_unit {L L' : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    (adj' : L' ⊣ R) {M M' : C} {N : D} (ξ : M ≅ M') (ψ : L'.obj M' ≅ N) (t : M ⟶ R.obj N)
    (ht : t = ξ.hom ≫ adj'.unit.app M' ≫ R.map ψ.hom) :
    IsIso ((adj.homEquiv M N).symm t) := by
  have hu : (adj.homEquiv M' (L'.obj M')).symm (adj'.unit.app M') =
      (Adjunction.leftAdjointUniq adj adj').hom.app M' := by
    rw [Equiv.symm_apply_eq, Adjunction.homEquiv_leftAdjointUniq_hom_app]
  rw [ht, Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_naturality_right_symm,
    hu]
  infer_instance

/-- **The square algebra of the flat base change of a quasi-coherent module**, in abstract
categories.  A natural transformation `comp : bR ⟶ bRA ⋙ R`, an isomorphism `g : A ≅ G`, and at
`A` the identification `h3C` of `comp` with a unit followed by an isomorphism: then the unit,
conjugated by the isomorphisms `ξ` and `ψ` assembled from these, is `comp` at `G` conjugated
by `eU` and `eW`. -/
theorem unit_conj_eq_comp_conj {C D D' : Type*} [Category C] [Category D] [Category D']
    {bR : C ⥤ D} {bRA : C ⥤ D'} {R : D' ⥤ D} (comp : bR ⟶ bRA ⋙ R) {A G : C} (g : A ≅ G)
    {M M' : D} {LM' P N : D'} (unit : M' ⟶ R.obj LM') (bc : P ≅ LM') (i1 : bR.obj A ≅ M')
    (i1' : bRA.obj A ≅ P) (eU : bR.obj G ≅ M) (eW : bRA.obj G ≅ N)
    (h3C : comp.app A ≫ R.map i1'.hom = i1.hom ≫ unit ≫ R.map bc.inv) :
    (eU.symm ≪≫ bR.mapIso g.symm ≪≫ i1).hom ≫ unit ≫
        R.map (bc.symm ≪≫ i1'.symm ≪≫ bRA.mapIso g ≪≫ eW).hom =
      eU.inv ≫ comp.app G ≫ R.map eW.hom := by
  have hnat := comp.naturality g.inv
  simp only [Functor.comp_map] at hnat
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.mapIso_inv,
    Functor.map_comp, Category.assoc]
  have h' : i1.hom ≫ unit ≫ R.map bc.inv ≫ R.map i1'.inv = comp.app A := by
    rw [← reassoc_of% h3C, ← R.map_comp, Iso.hom_inv_id, R.map_id, Category.comp_id]
  rw [reassoc_of% h', reassoc_of% hnat, ← R.map_comp_assoc, ← bRA.map_comp, Iso.inv_hom_id,
    bRA.map_id, R.map_id, Category.id_comp]

end Stacks.CategoryTheory.Adjunction

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type (u + 1)} [Category.{u} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- The two inverses of the localization functor `𝒳/x ⥤ (Sch/U)` at an object `x`: the one
`Functor.inv` chooses, which the restriction of Stacks 06WJ is built from, and the inverse of
`AlgebraicGeometry.FibredSite.localizationEquivalence`, which the inverse image `x^*` of
Stacks 06WI is built from.  The two equivalences have the same functor on the nose. -/
def overPostInvIsoLocalizationInverse (x : 𝒳) :
    letI := isEquivalence_overPost B S hS p hp x
    (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).inv ≅
      (FibredSite.localizationEquivalence B S hS p hp x).inverse :=
  letI := isEquivalence_overPost B S hS p hp x
  Stacks.CategoryTheory.Equivalence.inverseIsoOfFunctorIso
    (FibredSite.localizationEquivalence B S hS p hp x)
    (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).asEquivalence (Iso.refl _)

/-- `AlgebraicGeometry.Stack.overPostInvIsoLocalizationInverse` lies over the two counits. -/
theorem overPostInvIsoLocalizationInverse_hom_app_comp_counit (x : 𝒳)
    (T : Over (p.obj x).left) :
    letI := isEquivalence_overPost B S hS p hp x
    (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).map
        ((overPostInvIsoLocalizationInverse B S hS p hp x).hom.app T) ≫
      (FibredSite.localizationEquivalence B S hS p hp x).counit.app T =
    (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).asEquivalence.counit.app T := by
  let := isEquivalence_overPost B S hS p hp x
  refine (Stacks.CategoryTheory.Equivalence.functor_map_inverseIsoOfFunctorIso_hom_app_comp_counit
    (FibredSite.localizationEquivalence B S hS p hp x)
    (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).asEquivalence (Iso.refl _) T).trans ?_
  exact Category.id_comp _

/-- `AlgebraicGeometry.Stack.overPostInvIsoLocalizationInverse` lies over the two counits, with
the localization functor spelled as the functor of the localization equivalence. -/
theorem localizationEquivalence_functor_map_overPostInvIso_comp_counit (x : 𝒳)
    (T : Over (p.obj x).left) :
    letI := isEquivalence_overPost B S hS p hp x
    (FibredSite.localizationEquivalence B S hS p hp x).functor.map
        ((overPostInvIsoLocalizationInverse B S hS p hp x).hom.app T) ≫
      (FibredSite.localizationEquivalence B S hS p hp x).counit.app T =
    (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).asEquivalence.counit.app T :=
  overPostInvIsoLocalizationInverse_hom_app_comp_counit B S hS p hp x T

/-- The ring map below the small étale restriction of the inverse image `x^*F` of Stacks 06WI:
restriction of functions along the counit of the localization equivalence. -/
def objectInverseImageRestrictSharp (x : 𝒳) :
    (SmallEtale.structureSheaf (associatedBigEtaleSite B) (p.obj x).left.1
        (contains_base B (associatedBigEtaleSite B) rfl S hS p x)).obj ⟶
      (smallEtaleInclusion B (associatedBigEtaleSite B) rfl (p.obj x).left.1
          (contains_base B (associatedBigEtaleSite B) rfl S hS p x) ⋙
        (FibredSite.localizationEquivalence B S hS p hp x).inverse ⋙ Over.forget x).op ⋙
        (FibredSite.ringStructureSheafCore B S hS p hp .fppf).obj :=
  (𝟙 _ ≫ Functor.whiskerLeft (smallEtaleInclusion B (associatedBigEtaleSite B) rfl
      (p.obj x).left.1 (contains_base B (associatedBigEtaleSite B) rfl S hS p x)).op
    (Stacks.SheafOfModules.reindexBackSharp (J := BigFppfOver.baseOverTopology B
        (p.obj x).left.1 (p.obj x).left.2 .fppf)
      (J' := FibredSite.localizedTopologyKind B S hS p .fppf x)
      (FibredSite.localizationEquivalence B S hS p hp x)
      (FibredSite.baseRingStructureSheaf B (p.obj x).left.1 (p.obj x).left.2 .fppf)).hom) ≫
    Functor.whiskerLeft (smallEtaleInclusion B (associatedBigEtaleSite B) rfl (p.obj x).left.1
      (contains_base B (associatedBigEtaleSite B) rfl S hS p x) ⋙
        (FibredSite.localizationEquivalence B S hS p hp x).inverse).op
      (𝟙 ((FibredSite.ringStructureSheafCore B S hS p hp .fppf).over x).obj)

/-- The inverse image `x^*F` of Stacks 06WI on underlying presheaves of modules: restriction of
`F` to `𝒳/x`, then pushforward along the inverse of the localization equivalence. -/
theorem objectInverseImageKind_val
    (F : SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS p hp .fppf)) (x : 𝒳) :
    (FibredSite.objectInverseImageKind B S hS p hp .fppf x F).val =
      (PresheafOfModules.pushforward
        (F := (FibredSite.localizationEquivalence B S hS p hp x).inverse)
        (Stacks.SheafOfModules.reindexBackSharp (J := BigFppfOver.baseOverTopology B
            (p.obj x).left.1 (p.obj x).left.2 .fppf)
          (J' := FibredSite.localizedTopologyKind B S hS p .fppf x)
          (FibredSite.localizationEquivalence B S hS p hp x)
          (FibredSite.baseRingStructureSheaf B (p.obj x).left.1 (p.obj x).left.2 .fppf)).hom).obj
        ((PresheafOfModules.pushforward (F := Over.forget x)
          (𝟙 ((FibredSite.ringStructureSheafCore B S hS p hp .fppf).over x).obj)).obj F.val) :=
  rfl

/-- The small étale restriction of the inverse image `x^*F` of Stacks 06WI, as a single
pushforward of `F` along the composite functor. -/
def objectInverseImageRestrictValIso
    (F : SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS p hp .fppf)) (x : 𝒳) :
    (PresheafOfModules.pushforward
        (F := smallEtaleInclusion B (associatedBigEtaleSite B) rfl (p.obj x).left.1
          (contains_base B (associatedBigEtaleSite B) rfl S hS p x)) (𝟙 _)).obj
        (FibredSite.objectInverseImageKind B S hS p hp .fppf x F).val ≅
      (PresheafOfModules.pushforward (objectInverseImageRestrictSharp B S hS p hp x)).obj F.val :=
  eqToIso (congrArg (PresheafOfModules.pushforward
        (F := smallEtaleInclusion B (associatedBigEtaleSite B) rfl (p.obj x).left.1
          (contains_base B (associatedBigEtaleSite B) rfl S hS p x)) (𝟙 _)).obj
      (objectInverseImageKind_val B S hS p hp F x)) ≪≫
    (PresheafOfModules.pushforwardComp
      (F := smallEtaleInclusion B (associatedBigEtaleSite B) rfl (p.obj x).left.1
          (contains_base B (associatedBigEtaleSite B) rfl S hS p x))
      (G := (FibredSite.localizationEquivalence B S hS p hp x).inverse)
      (𝟙 _) (Stacks.SheafOfModules.reindexBackSharp (J := BigFppfOver.baseOverTopology B
        (p.obj x).left.1 (p.obj x).left.2 .fppf)
      (J' := FibredSite.localizedTopologyKind B S hS p .fppf x)
      (FibredSite.localizationEquivalence B S hS p hp x)
      (FibredSite.baseRingStructureSheaf B (p.obj x).left.1 (p.obj x).left.2 .fppf)).hom).app
      ((PresheafOfModules.pushforward (F := Over.forget x)
          (𝟙 ((FibredSite.ringStructureSheafCore B S hS p hp .fppf).over x).obj)).obj F.val) ≪≫
    (PresheafOfModules.pushforwardComp
      (F := smallEtaleInclusion B (associatedBigEtaleSite B) rfl (p.obj x).left.1
          (contains_base B (associatedBigEtaleSite B) rfl S hS p x) ⋙
        (FibredSite.localizationEquivalence B S hS p hp x).inverse)
      (G := Over.forget x) _
      (𝟙 ((FibredSite.ringStructureSheafCore B S hS p hp .fppf).over x).obj)).app F.val

omit [Category.{u} 𝒳] in
/-- Global functions pulled back along a composite in a slice of the schemes of `B`, as the
composite of the two pullbacks. -/
theorem Γ_map_inclusion_left_of_comp_eq {Y : B.Schemes} {T₁ T₂ T₃ : Over Y} (f : T₁ ⟶ T₂)
    (g : T₂ ⟶ T₃) {k : T₁ ⟶ T₃} (hk : f ≫ g = k) :
    Scheme.Γ.map (B.inclusion.map k.left).op =
      Scheme.Γ.map (B.inclusion.map g.left).op ≫ Scheme.Γ.map (B.inclusion.map f.left).op := by
  rw [← hk, Over.comp_left, Functor.map_comp, op_comp, Functor.map_comp]

/-- The two ring maps below the two restrictions of `F` to the small étale site of `U` agree
along the canonical isomorphism of lifts: both are restriction of functions along a counit. -/
theorem objectInverseImageRestrictSharp_compat (x : 𝒳)
    (V : (SmallEtale (associatedBigEtaleSite B) (p.obj x).left.1
      (contains_base B (associatedBigEtaleSite B) rfl S hS p x))ᵒᵖ)
    (r : (SmallEtale.structureSheaf (associatedBigEtaleSite B) (p.obj x).left.1
      (contains_base B (associatedBigEtaleSite B) rfl S hS p x)).obj.obj V) :
    letI := isEquivalence_overPost B S hS p hp x
    ((FibredSite.ringStructureSheafCore B S hS p hp .fppf).obj.map
      ((Functor.isoWhiskerLeft (smallEtaleInclusion B (associatedBigEtaleSite B) rfl
          (p.obj x).left.1 (contains_base B (associatedBigEtaleSite B) rfl S hS p x))
        (Functor.isoWhiskerRight (overPostInvIsoLocalizationInverse B S hS p hp x)
          (Over.forget x))).hom.app V.unop).op).hom
        (((objectInverseImageRestrictSharp B S hS p hp x).app V).hom r) =
      ((localStructurePresheafIso B (associatedBigEtaleSite B) rfl S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B)).hom.app V).hom r := by
  let := isEquivalence_overPost B S hS p hp x
  show (Scheme.Γ.map (B.inclusion.map ((Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).map
        ((overPostInvIsoLocalizationInverse B S hS p hp x).hom.app
          ((smallEtaleInclusion B (associatedBigEtaleSite B) rfl (p.obj x).left.1
            (contains_base B (associatedBigEtaleSite B) rfl S hS p x)).obj V.unop))).left).op).hom
      ((Scheme.Γ.map (B.inclusion.map ((FibredSite.localizationEquivalence B S hS p hp x).counit.app
          ((smallEtaleInclusion B (associatedBigEtaleSite B) rfl (p.obj x).left.1
            (contains_base B (associatedBigEtaleSite B) rfl S hS p x)).obj
              V.unop)).left).op).hom r) =
    (Scheme.Γ.map (B.inclusion.map
      ((Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).asEquivalence.counit.app
          ((smallEtaleInclusion B (associatedBigEtaleSite B) rfl (p.obj x).left.1
            (contains_base B (associatedBigEtaleSite B) rfl S hS p x)).obj V.unop)).left).op).hom r
  exact (congrArg (fun φ => φ.hom r) (Γ_map_inclusion_left_of_comp_eq B _ _
    (overPostInvIsoLocalizationInverse_hom_app_comp_counit B S hS p hp x
      ((smallEtaleInclusion B (associatedBigEtaleSite B) rfl (p.obj x).left.1
        (contains_base B (associatedBigEtaleSite B) rfl S hS p x)).obj V.unop)))).symm

/-- **The restriction of Stacks 06WJ is the small étale restriction of the inverse image of
Stacks 06WI.**  For a sheaf of modules `F` on the associated fppf site of `𝒳` and an object `x`
over a scheme `U`, the restriction to the small étale site of `U` of `x^*F` on `(Sch/U)_fppf`
is the restriction `F|_{U_ét}`.  On sections over `V` étale over `U` it is restriction of `F`
along the canonical isomorphism between the two chosen lifts of `V ⟶ U` to `𝒳/x`. -/
def objectInverseImageRestrictIso
    (F : SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS p hp .fppf)) (x : 𝒳) :
    (PresheafOfModules.pushforward
        (F := smallEtaleInclusion B (associatedBigEtaleSite B) rfl (p.obj x).left.1
          (contains_base B (associatedBigEtaleSite B) rfl S hS p x)) (𝟙 _)).obj
        (FibredSite.objectInverseImageKind B S hS p hp .fppf x F).val ≅
      restrictModuleToSmallEtale B (associatedBigEtaleSite B) rfl S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F.val :=
  letI := isEquivalence_overPost B S hS p hp x
  objectInverseImageRestrictValIso B S hS p hp F x ≪≫
    Stacks.PresheafOfModules.restrictScalarsPushforward₀Iso F.val
      (Functor.isoWhiskerLeft (smallEtaleInclusion B (associatedBigEtaleSite B) rfl
          (p.obj x).left.1 (contains_base B (associatedBigEtaleSite B) rfl S hS p x))
        (Functor.isoWhiskerRight (overPostInvIsoLocalizationInverse B S hS p hp x)
          (Over.forget x)))
      (localStructurePresheafIso B (associatedBigEtaleSite B) rfl S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B)).hom (objectInverseImageRestrictSharp B S hS p hp x)
      (objectInverseImageRestrictSharp_compat B S hS p hp x)

/-- The lift of a scheme over `W` to `𝒳/z`, followed by `φ : z ⟶ x` and the localization
functor at `x`, is the scheme regarded over `U` through `a : W ⟶ U`. -/
def overPostInvMapCompIso {x z : 𝒳} (φ : z ⟶ x) :
    letI := isEquivalence_overPost B S hS p hp z
    ((Over.post (X := z) (p ⋙ Over.forget (B.obj hS))).inv ⋙ Over.map φ) ⋙
        (FibredSite.localizationEquivalence B S hS p hp x).functor ≅
      Over.map (p.map φ).left :=
  letI := isEquivalence_overPost B S hS p hp z
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Over.mapCompPostIso (p ⋙ Over.forget (B.obj hS)) φ) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Over.post (X := z) (p ⋙ Over.forget (B.obj hS))).asEquivalence.counitIso
      (Over.map (p.map φ).left) ≪≫ Functor.leftUnitor _

/-- `AlgebraicGeometry.Stack.overPostInvMapCompIso` is the counit of the localization
equivalence at `z` on the underlying schemes. -/
theorem overPostInvMapCompIso_hom_app_left {x z : 𝒳} (φ : z ⟶ x) (T : Over (p.obj z).left) :
    letI := isEquivalence_overPost B S hS p hp z
    ((overPostInvMapCompIso B S hS p hp φ).hom.app T).left =
      ((Over.post (X := z) (p ⋙ Over.forget (B.obj hS))).asEquivalence.counit.app T).left := by
  let := isEquivalence_overPost B S hS p hp z
  simp only [overPostInvMapCompIso, Iso.trans_hom, NatTrans.comp_app]
  show 𝟙 _ ≫ (𝟙 _ ≫ ((Over.post (X := z) (p ⋙ Over.forget (B.obj hS))).asEquivalence.counit.app
    T).left ≫ 𝟙 _) ≫ 𝟙 _ = _
  simp only [Category.id_comp, Category.comp_id]
/-- **The two lifts below an arrow.**  For `φ : z ⟶ x` lying over `a : W ⟶ U`, a scheme `T`
over `W` has two lifts to `𝒳/x`: the lift of `T` to `𝒳/z` chosen by `Functor.inv`, followed by
`φ`, and the lift of `T ⟶ W ⟶ U` chosen by the inverse of the localization equivalence at `x`.
They are canonically isomorphic. -/
def overPostInvMapIsoLocalizationInverse {x z : 𝒳} (φ : z ⟶ x) :
    letI := isEquivalence_overPost B S hS p hp z
    (Over.post (X := z) (p ⋙ Over.forget (B.obj hS))).inv ⋙ Over.map φ ≅
      Over.map (p.map φ).left ⋙ (FibredSite.localizationEquivalence B S hS p hp x).inverse :=
  letI := isEquivalence_overPost B S hS p hp z
  Stacks.CategoryTheory.Equivalence.isoCompInverseOfIso
    (FibredSite.localizationEquivalence B S hS p hp x) (overPostInvMapCompIso B S hS p hp φ)

/-- The first stage of `AlgebraicGeometry.Stack.objectInverseImageRestrictAlongSharp`: the
identity of the structure sheaf of the small étale site of `W`, seen through `Over.map a`. -/
def objectInverseImageRestrictAlongSharp₁ {x z : 𝒳} (φ : z ⟶ x) :
    (SmallEtale.structureSheaf (associatedBigEtaleSite B) (p.obj z).left.1
        (contains_base B (associatedBigEtaleSite B) rfl S hS p z)).obj ⟶
      (smallEtaleInclusion B (associatedBigEtaleSite B) rfl (p.obj z).left.1
          (contains_base B (associatedBigEtaleSite B) rfl S hS p z) ⋙
          Over.map (p.map φ).left).op ⋙
        (FibredSite.baseRingStructureSheaf B (p.obj x).left.1 (p.obj x).left.2 .fppf).obj :=
  𝟙 _ ≫ Functor.whiskerLeft (smallEtaleInclusion B (associatedBigEtaleSite B) rfl
      (p.obj z).left.1 (contains_base B (associatedBigEtaleSite B) rfl S hS p z)).op
    (𝟙 (FibredSite.baseRingStructureSheaf B (p.obj z).left.1 (p.obj z).left.2 .fppf).obj)

/-- The ring map below the restriction of the inverse image `x^*F` of Stacks 06WI to the small
étale site of `W` along `a : W ⟶ U`: restriction of functions along the counit of the
localization equivalence at `x`. -/
def objectInverseImageRestrictAlongSharp {x z : 𝒳} (φ : z ⟶ x) :
    (SmallEtale.structureSheaf (associatedBigEtaleSite B) (p.obj z).left.1
        (contains_base B (associatedBigEtaleSite B) rfl S hS p z)).obj ⟶
      (((smallEtaleInclusion B (associatedBigEtaleSite B) rfl (p.obj z).left.1
          (contains_base B (associatedBigEtaleSite B) rfl S hS p z) ⋙
          Over.map (p.map φ).left) ⋙
        (FibredSite.localizationEquivalence B S hS p hp x).inverse) ⋙ Over.forget x).op ⋙
        (FibredSite.ringStructureSheafCore B S hS p hp .fppf).obj :=
  (objectInverseImageRestrictAlongSharp₁ B S hS p φ ≫
    Functor.whiskerLeft (smallEtaleInclusion B (associatedBigEtaleSite B) rfl (p.obj z).left.1
      (contains_base B (associatedBigEtaleSite B) rfl S hS p z) ⋙ Over.map (p.map φ).left).op
    (Stacks.SheafOfModules.reindexBackSharp (J := BigFppfOver.baseOverTopology B
        (p.obj x).left.1 (p.obj x).left.2 .fppf)
      (J' := FibredSite.localizedTopologyKind B S hS p .fppf x)
      (FibredSite.localizationEquivalence B S hS p hp x)
      (FibredSite.baseRingStructureSheaf B (p.obj x).left.1 (p.obj x).left.2 .fppf)).hom) ≫
    Functor.whiskerLeft ((smallEtaleInclusion B (associatedBigEtaleSite B) rfl (p.obj z).left.1
      (contains_base B (associatedBigEtaleSite B) rfl S hS p z) ⋙ Over.map (p.map φ).left) ⋙
        (FibredSite.localizationEquivalence B S hS p hp x).inverse).op
      (𝟙 ((FibredSite.ringStructureSheafCore B S hS p hp .fppf).over x).obj)

/-- The restriction along `a : W ⟶ U` of the inverse image `x^*F` to the small étale site of
`W`, as a single pushforward of `F` along the composite functor. -/
def objectInverseImageRestrictAlongValIso
    (F : SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS p hp .fppf)) {x z : 𝒳}
    (φ : z ⟶ x) :
    (PresheafOfModules.pushforward
        (F := smallEtaleInclusion B (associatedBigEtaleSite B) rfl (p.obj z).left.1
          (contains_base B (associatedBigEtaleSite B) rfl S hS p z))
        (𝟙 (SmallEtale.structureSheaf (associatedBigEtaleSite B) (p.obj z).left.1
          (contains_base B (associatedBigEtaleSite B) rfl S hS p z)).obj)).obj
        ((PresheafOfModules.pushforward (F := Over.map (p.map φ).left)
          (𝟙 (FibredSite.baseRingStructureSheaf B (p.obj z).left.1 (p.obj z).left.2 .fppf).obj)).obj
          (FibredSite.objectInverseImageKind B S hS p hp .fppf x F).val) ≅
      (PresheafOfModules.pushforward (objectInverseImageRestrictAlongSharp B S hS p hp φ)).obj
        F.val := by
  refine (PresheafOfModules.pushforward
      (F := smallEtaleInclusion B (associatedBigEtaleSite B) rfl (p.obj z).left.1
        (contains_base B (associatedBigEtaleSite B) rfl S hS p z)) (𝟙 _)).mapIso
    ((PresheafOfModules.pushforward (F := Over.map (p.map φ).left) (𝟙 _)).mapIso
      (eqToIso (objectInverseImageKind_val B S hS p hp F x))) ≪≫ ?_
  refine (PresheafOfModules.pushforwardComp
      (F := smallEtaleInclusion B (associatedBigEtaleSite B) rfl (p.obj z).left.1
          (contains_base B (associatedBigEtaleSite B) rfl S hS p z))
      (G := Over.map (p.map φ).left) _ _).app _ ≪≫ ?_
  refine (PresheafOfModules.pushforwardComp
      (F := smallEtaleInclusion B (associatedBigEtaleSite B) rfl (p.obj z).left.1
          (contains_base B (associatedBigEtaleSite B) rfl S hS p z) ⋙ Over.map (p.map φ).left)
      (G := (FibredSite.localizationEquivalence B S hS p hp x).inverse) _ _).app _ ≪≫ ?_
  exact (PresheafOfModules.pushforwardComp
      (F := (smallEtaleInclusion B (associatedBigEtaleSite B) rfl (p.obj z).left.1
          (contains_base B (associatedBigEtaleSite B) rfl S hS p z) ⋙
          Over.map (p.map φ).left) ⋙ (FibredSite.localizationEquivalence B S hS p hp x).inverse)
      (G := Over.forget x) _ _).app F.val

/-- The ring maps below the restriction `F|_{W_ét}` and below the restriction along
`a : W ⟶ U` of the inverse image `x^*F` agree along the canonical isomorphism of lifts. -/
theorem objectInverseImageRestrictAlongSharp_compat {x z : 𝒳} (φ : z ⟶ x)
    (V : (SmallEtale (associatedBigEtaleSite B) (p.obj z).left.1
      (contains_base B (associatedBigEtaleSite B) rfl S hS p z))ᵒᵖ)
    (r : (SmallEtale.structureSheaf (associatedBigEtaleSite B) (p.obj z).left.1
      (contains_base B (associatedBigEtaleSite B) rfl S hS p z)).obj.obj V) :
    letI := isEquivalence_overPost B S hS p hp z
    ((FibredSite.ringStructureSheafCore B S hS p hp .fppf).obj.map
      ((Functor.isoWhiskerLeft (smallEtaleInclusion B (associatedBigEtaleSite B) rfl
          (p.obj z).left.1 (contains_base B (associatedBigEtaleSite B) rfl S hS p z))
        (Functor.isoWhiskerRight (overPostInvMapIsoLocalizationInverse B S hS p hp φ)
          (Over.forget x))).hom.app V.unop).op).hom
        (((objectInverseImageRestrictAlongSharp B S hS p hp φ).app V).hom r) =
      ((localStructurePresheafIso B (associatedBigEtaleSite B) rfl S hS p hp z (etaleTopology B)
        (etaleTopology_le_topology B)).hom.app V).hom r := by
  let := isEquivalence_overPost B S hS p hp z
  have h := Γ_map_inclusion_left_of_comp_eq B _ _
    (Stacks.CategoryTheory.Equivalence.functor_map_isoCompInverseOfIso_hom_app_comp_counit
      (FibredSite.localizationEquivalence B S hS p hp x) (overPostInvMapCompIso B S hS p hp φ)
      ((smallEtaleInclusion B (associatedBigEtaleSite B) rfl (p.obj z).left.1
        (contains_base B (associatedBigEtaleSite B) rfl S hS p z)).obj V.unop))
  rw [overPostInvMapCompIso_hom_app_left] at h
  exact (congrArg (fun φ => φ.hom r) h).symm

/-- **The restriction of Stacks 06WJ at the source of an arrow, from the inverse image at its
target.**  For `φ : z ⟶ x` lying over `a : W ⟶ U`, the restriction `F|_{W_ét}` is the
restriction to the small étale site of `W`, along `a`, of the inverse image `x^*F` of
Stacks 06WI on `(Sch/U)_fppf`.  On sections over `V` étale over `W` it is restriction of `F`
along the canonical isomorphism between the lift of `V` to `𝒳/z` followed by `φ` and the lift
of `V ⟶ W ⟶ U` to `𝒳/x`. -/
def objectInverseImageRestrictAlongIso
    (F : SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS p hp .fppf)) {x z : 𝒳}
    (φ : z ⟶ x) :
    (PresheafOfModules.pushforward
        (F := smallEtaleInclusion B (associatedBigEtaleSite B) rfl (p.obj z).left.1
          (contains_base B (associatedBigEtaleSite B) rfl S hS p z))
        (𝟙 (SmallEtale.structureSheaf (associatedBigEtaleSite B) (p.obj z).left.1
          (contains_base B (associatedBigEtaleSite B) rfl S hS p z)).obj)).obj
        ((PresheafOfModules.pushforward (F := Over.map (p.map φ).left)
          (𝟙 (FibredSite.baseRingStructureSheaf B (p.obj z).left.1 (p.obj z).left.2 .fppf).obj)).obj
          (FibredSite.objectInverseImageKind B S hS p hp .fppf x F).val) ≅
      restrictModuleToSmallEtale B (associatedBigEtaleSite B) rfl S hS p hp z (etaleTopology B)
        (etaleTopology_le_topology B) F.val :=
  letI := isEquivalence_overPost B S hS p hp z
  objectInverseImageRestrictAlongValIso B S hS p hp F φ ≪≫
    Stacks.PresheafOfModules.restrictScalarsPushforward₀Iso F.val
      (Functor.isoWhiskerLeft (smallEtaleInclusion B (associatedBigEtaleSite B) rfl
          (p.obj z).left.1 (contains_base B (associatedBigEtaleSite B) rfl S hS p z))
        (Functor.isoWhiskerRight (overPostInvMapIsoLocalizationInverse B S hS p hp φ)
          (Over.forget x)))
      (localStructurePresheafIso B (associatedBigEtaleSite B) rfl S hS p hp z (etaleTopology B)
        (etaleTopology_le_topology B)).hom (objectInverseImageRestrictAlongSharp B S hS p hp φ)
      (objectInverseImageRestrictAlongSharp_compat B S hS p hp φ)

/-- `AlgebraicGeometry.Stack.objectInverseImageRestrictIso` on sections: restriction of `F`
along the canonical isomorphism of lifts. -/
theorem objectInverseImageRestrictIso_hom_app_apply
    (F : SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS p hp .fppf)) (x : 𝒳)
    (V : (SmallEtale (associatedBigEtaleSite B) (p.obj x).left.1
      (contains_base B (associatedBigEtaleSite B) rfl S hS p x))ᵒᵖ)
    (m : F.val.obj (Opposite.op ((FibredSite.localizationEquivalence B S hS p hp x).inverse.obj
      ((smallEtaleInclusion B (associatedBigEtaleSite B) rfl (p.obj x).left.1
        (contains_base B (associatedBigEtaleSite B) rfl S hS p x)).obj V.unop)).left)) :
    (objectInverseImageRestrictIso B S hS p hp F x).hom.app V m =
      F.val.map ((overPostInvIsoLocalizationInverse B S hS p hp x).hom.app
        ((smallEtaleInclusion B (associatedBigEtaleSite B) rfl (p.obj x).left.1
          (contains_base B (associatedBigEtaleSite B) rfl S hS p x)).obj V.unop)).left.op m :=
  rfl

/-- **The comparison arrow of Stacks 06W2, through the inverse image.**  For `φ : z ⟶ x` over
`a : W ⟶ U`, an object `V` of the small étale site of `U` and its base change `V ×_U W`, the
arrow `φ'` of `𝒳` computing the comparison of Stacks 06W2 at `V`, followed by the canonical
isomorphism of lifts at `x`, is the canonical isomorphism of lifts at the base change followed by
the lift to `𝒳/x` of the base-change projection `π : V ×_U W ⟶ V`. -/
theorem comparisonLift_comp_overPostInvIso {x z : 𝒳} (φ : z ⟶ x)
    (V : SmallEtale (associatedBigEtaleSite B) (p.obj x).left.1
      (contains_base B (associatedBigEtaleSite B) rfl S hS p x))
    (φ' : ((letI := isEquivalence_overPost B S hS p hp z;
        (Over.post (X := z) (p ⋙ Over.forget (B.obj hS))).inv.obj
          ((smallEtaleInclusion B (associatedBigEtaleSite B) rfl (p.obj z).left.1
            (contains_base B (associatedBigEtaleSite B) rfl S hS p z)).obj
            ((smallEtaleBaseChange (associatedBigEtaleSite B)
              (smallEtaleBaseMorphism B (associatedBigEtaleSite B) rfl S hS p φ)).obj V)))).left ⟶
      ((letI := isEquivalence_overPost B S hS p hp x;
        (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).inv.obj
          ((smallEtaleInclusion B (associatedBigEtaleSite B) rfl (p.obj x).left.1
            (contains_base B (associatedBigEtaleSite B) rfl S hS p x)).obj V))).left)
    (hsq : letI := isEquivalence_overPost B S hS p hp z
      letI := isEquivalence_overPost B S hS p hp x
      φ' ≫ ((Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).inv.obj
          ((smallEtaleInclusion B (associatedBigEtaleSite B) rfl (p.obj x).left.1
            (contains_base B (associatedBigEtaleSite B) rfl S hS p x)).obj V)).hom =
        ((Over.post (X := z) (p ⋙ Over.forget (B.obj hS))).inv.obj
          ((smallEtaleInclusion B (associatedBigEtaleSite B) rfl (p.obj z).left.1
            (contains_base B (associatedBigEtaleSite B) rfl S hS p z)).obj
            ((smallEtaleBaseChange (associatedBigEtaleSite B)
              (smallEtaleBaseMorphism B (associatedBigEtaleSite B) rfl S hS p φ)).obj V))).hom ≫ φ)
    (π : (Over.map (p.map φ).left).obj
        ((smallEtaleInclusion B (associatedBigEtaleSite B) rfl (p.obj z).left.1
          (contains_base B (associatedBigEtaleSite B) rfl S hS p z)).obj
          ((smallEtaleBaseChange (associatedBigEtaleSite B)
            (smallEtaleBaseMorphism B (associatedBigEtaleSite B) rfl S hS p φ)).obj V)) ⟶
      (smallEtaleInclusion B (associatedBigEtaleSite B) rfl (p.obj x).left.1
        (contains_base B (associatedBigEtaleSite B) rfl S hS p x)).obj V)
    (hproj : letI := isEquivalence_overPost B S hS p hp z
      letI := isEquivalence_overPost B S hS p hp x
      (p.map φ').left ≫ ((Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).asEquivalence.counit.app
          ((smallEtaleInclusion B (associatedBigEtaleSite B) rfl (p.obj x).left.1
            (contains_base B (associatedBigEtaleSite B) rfl S hS p x)).obj V)).left =
        ((Over.post (X := z) (p ⋙ Over.forget (B.obj hS))).asEquivalence.counit.app
          ((smallEtaleInclusion B (associatedBigEtaleSite B) rfl (p.obj z).left.1
            (contains_base B (associatedBigEtaleSite B) rfl S hS p z)).obj
            ((smallEtaleBaseChange (associatedBigEtaleSite B)
              (smallEtaleBaseMorphism B (associatedBigEtaleSite B) rfl S hS p φ)).obj V))).left ≫
          π.left) :
    φ' ≫ ((overPostInvIsoLocalizationInverse B S hS p hp x).hom.app
        ((smallEtaleInclusion B (associatedBigEtaleSite B) rfl (p.obj x).left.1
          (contains_base B (associatedBigEtaleSite B) rfl S hS p x)).obj V)).left =
      ((overPostInvMapIsoLocalizationInverse B S hS p hp φ).hom.app
        ((smallEtaleInclusion B (associatedBigEtaleSite B) rfl (p.obj z).left.1
          (contains_base B (associatedBigEtaleSite B) rfl S hS p z)).obj
          ((smallEtaleBaseChange (associatedBigEtaleSite B)
            (smallEtaleBaseMorphism B (associatedBigEtaleSite B) rfl S hS p φ)).obj V))).left ≫
        ((FibredSite.localizationEquivalence B S hS p hp x).inverse.map π).left := by
  let := isEquivalence_overPost B S hS p hp z
  let := isEquivalence_overPost B S hS p hp x
  let lhs : (Over.map φ).obj ((Over.post (X := z) (p ⋙ Over.forget (B.obj hS))).inv.obj
      ((smallEtaleInclusion B (associatedBigEtaleSite B) rfl (p.obj z).left.1
          (contains_base B (associatedBigEtaleSite B) rfl S hS p z)).obj
          ((smallEtaleBaseChange (associatedBigEtaleSite B)
            (smallEtaleBaseMorphism B (associatedBigEtaleSite B) rfl S hS p φ)).obj V))) ⟶
      (FibredSite.localizationEquivalence B S hS p hp x).inverse.obj
        ((smallEtaleInclusion B (associatedBigEtaleSite B) rfl (p.obj x).left.1
          (contains_base B (associatedBigEtaleSite B) rfl S hS p x)).obj V) :=
    Over.homMk φ' hsq ≫ (overPostInvIsoLocalizationInverse B S hS p hp x).hom.app _
  let rhs : (Over.map φ).obj ((Over.post (X := z) (p ⋙ Over.forget (B.obj hS))).inv.obj
      ((smallEtaleInclusion B (associatedBigEtaleSite B) rfl (p.obj z).left.1
          (contains_base B (associatedBigEtaleSite B) rfl S hS p z)).obj
          ((smallEtaleBaseChange (associatedBigEtaleSite B)
            (smallEtaleBaseMorphism B (associatedBigEtaleSite B) rfl S hS p φ)).obj V))) ⟶
      (FibredSite.localizationEquivalence B S hS p hp x).inverse.obj
        ((smallEtaleInclusion B (associatedBigEtaleSite B) rfl (p.obj x).left.1
          (contains_base B (associatedBigEtaleSite B) rfl S hS p x)).obj V) :=
    (overPostInvMapIsoLocalizationInverse B S hS p hp φ).hom.app _ ≫
      (FibredSite.localizationEquivalence B S hS p hp x).inverse.map π
  suffices hlr : lhs = rhs from congrArg CommaMorphism.left hlr
  apply (FibredSite.localizationEquivalence B S hS p hp x).functor.map_injective
  rw [← cancel_mono ((FibredSite.localizationEquivalence B S hS p hp x).counit.app _)]
  have h1 : (FibredSite.localizationEquivalence B S hS p hp x).functor.map lhs ≫
        (FibredSite.localizationEquivalence B S hS p hp x).counit.app _ =
      (FibredSite.localizationEquivalence B S hS p hp x).functor.map (Over.homMk φ' hsq) ≫
        (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).asEquivalence.counit.app _ := by
    simp only [lhs, Functor.map_comp, Category.assoc]
    rw [localizationEquivalence_functor_map_overPostInvIso_comp_counit]
  have h2 : (FibredSite.localizationEquivalence B S hS p hp x).functor.map rhs ≫
        (FibredSite.localizationEquivalence B S hS p hp x).counit.app _ =
      (overPostInvMapCompIso B S hS p hp φ).hom.app _ ≫ π := by
    have k : (FibredSite.localizationEquivalence B S hS p hp x).functor.map
        ((overPostInvMapIsoLocalizationInverse B S hS p hp φ).hom.app
          ((smallEtaleInclusion B (associatedBigEtaleSite B) rfl (p.obj z).left.1
            (contains_base B (associatedBigEtaleSite B) rfl S hS p z)).obj
            ((smallEtaleBaseChange (associatedBigEtaleSite B)
              (smallEtaleBaseMorphism B (associatedBigEtaleSite B) rfl S hS p φ)).obj V))) ≫
          (FibredSite.localizationEquivalence B S hS p hp x).counit.app _ =
        (overPostInvMapCompIso B S hS p hp φ).hom.app _ :=
      Stacks.CategoryTheory.Equivalence.functor_map_isoCompInverseOfIso_hom_app_comp_counit
        (FibredSite.localizationEquivalence B S hS p hp x) (overPostInvMapCompIso B S hS p hp φ) _
    have k' := (FibredSite.localizationEquivalence B S hS p hp x).counit_naturality π
    simp only [Functor.comp_obj, Functor.id_obj] at k'
    simp only [rhs, Functor.map_comp, Category.assoc]
    rw [k', ← Category.assoc, k]
  rw [h1, h2]
  apply Over.OverMorphism.ext
  refine Eq.trans ?_ (hproj.trans ?_)
  · rfl
  · rw [Over.comp_left, overPostInvMapCompIso_hom_app_left]
    rfl

/-- `AlgebraicGeometry.Stack.objectInverseImageRestrictAlongIso` on sections: restriction of
`F` along the canonical isomorphism of lifts. -/
theorem objectInverseImageRestrictAlongIso_hom_app_apply
    (F : SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS p hp .fppf)) {x z : 𝒳}
    (φ : z ⟶ x)
    (V : (SmallEtale (associatedBigEtaleSite B) (p.obj z).left.1
      (contains_base B (associatedBigEtaleSite B) rfl S hS p z))ᵒᵖ)
    (m : F.val.obj (Opposite.op ((FibredSite.localizationEquivalence B S hS p hp x).inverse.obj
      ((Over.map (p.map φ).left).obj
        ((smallEtaleInclusion B (associatedBigEtaleSite B) rfl (p.obj z).left.1
          (contains_base B (associatedBigEtaleSite B) rfl S hS p z)).obj V.unop))).left)) :
    (objectInverseImageRestrictAlongIso B S hS p hp F φ).hom.app V m =
      F.val.map ((overPostInvMapIsoLocalizationInverse B S hS p hp φ).hom.app
        ((smallEtaleInclusion B (associatedBigEtaleSite B) rfl (p.obj z).left.1
          (contains_base B (associatedBigEtaleSite B) rfl S hS p z)).obj V.unop)).left.op m :=
  rfl

/-- The restriction maps of the inverse image `x^*F` of Stacks 06WI are restriction maps of `F`
along the lifts to `𝒳/x`. -/
theorem objectInverseImageKind_val_map_apply
    (F : SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS p hp .fppf)) (x : 𝒳)
    {T T' : Over (p.obj x).left} (π : T ⟶ T')
    (m : F.val.obj (Opposite.op ((FibredSite.localizationEquivalence B S hS p hp x).inverse.obj
      T').left)) :
    (FibredSite.objectInverseImageKind B S hS p hp .fppf x F).val.map π.op m =
      F.val.map ((FibredSite.localizationEquivalence B S hS p hp x).inverse.map π).left.op m :=
  rfl

/-- **The comparison of Stacks 06W2 through the inverse image.**  For `φ : z ⟶ x` over
`a : W ⟶ U` and `V` étale over `U`, the comparison `F|_{U_ét}(V) ⟶ F|_{W_ét}(V ×_U W)` of
Stacks 06W2 is, under the identifications of
`AlgebraicGeometry.Stack.objectInverseImageRestrictIso` and
`AlgebraicGeometry.Stack.objectInverseImageRestrictAlongIso`, the restriction of the inverse
image `x^*F` along any lift `π` to the schemes over `U` of the base-change projection
`V ×_U W ⟶ V`. -/
theorem restrictionPushforwardComparison_objectInverseImageRestrictIso
    (F : SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS p hp .fppf)) {x z : 𝒳}
    (φ : z ⟶ x)
    (V : SmallEtale (associatedBigEtaleSite B) (p.obj x).left.1
      (contains_base B (associatedBigEtaleSite B) rfl S hS p x))
    (π : (Over.map (p.map φ).left).obj
        ((smallEtaleInclusion B (associatedBigEtaleSite B) rfl (p.obj z).left.1
          (contains_base B (associatedBigEtaleSite B) rfl S hS p z)).obj
          ((smallEtaleBaseChange (associatedBigEtaleSite B)
            (smallEtaleBaseMorphism B (associatedBigEtaleSite B) rfl S hS p φ)).obj V)) ⟶
      (smallEtaleInclusion B (associatedBigEtaleSite B) rfl (p.obj x).left.1
        (contains_base B (associatedBigEtaleSite B) rfl S hS p x)).obj V)
    (hπ : B.inclusion.map π.left = (associatedBigEtaleSite B).inclusion.map
      (Limits.pullback.fst V.obj.hom
        (smallEtaleBaseMorphism B (associatedBigEtaleSite B) rfl S hS p φ)))
    (m : F.val.obj (Opposite.op ((FibredSite.localizationEquivalence B S hS p hp x).inverse.obj
      ((smallEtaleInclusion B (associatedBigEtaleSite B) rfl (p.obj x).left.1
        (contains_base B (associatedBigEtaleSite B) rfl S hS p x)).obj V)).left)) :
    (restrictionPushforwardComparison B (associatedBigEtaleSite B) rfl S hS p hp φ
        F.val.presheaf).app (Opposite.op V)
        ((objectInverseImageRestrictIso B S hS p hp F x).hom.app (Opposite.op V) m) =
      (objectInverseImageRestrictAlongIso B S hS p hp F φ).hom.app
        (Opposite.op ((smallEtaleBaseChange (associatedBigEtaleSite B)
          (smallEtaleBaseMorphism B (associatedBigEtaleSite B) rfl S hS p φ)).obj V))
        ((FibredSite.objectInverseImageKind B S hS p hp .fppf x F).val.map π.op m) := by
  obtain ⟨φ', hsq, hproj⟩ :=
    exists_restrictionComparisonLift B (associatedBigEtaleSite B) rfl S hS p hp φ V
  have key := comparisonLift_comp_overPostInvIso B S hS p hp φ V φ' hsq π
    (B.inclusion.map_injective (by
      simp only [Functor.map_comp]
      exact hproj.trans (congrArg (fun g => _ ≫ g) hπ.symm)))
  have hκ := restrictionPushforwardComparison_app B (associatedBigEtaleSite B) rfl S hS p hp φ
    F.val.presheaf V φ' hsq hproj
  rw [hκ, objectInverseImageRestrictIso_hom_app_apply]
  have hR : (objectInverseImageRestrictAlongIso B S hS p hp F φ).hom.app
      (Opposite.op ((smallEtaleBaseChange (associatedBigEtaleSite B)
        (smallEtaleBaseMorphism B (associatedBigEtaleSite B) rfl S hS p φ)).obj V))
      ((FibredSite.objectInverseImageKind B S hS p hp .fppf x F).val.map π.op m) =
    F.val.map ((overPostInvMapIsoLocalizationInverse B S hS p hp φ).hom.app
        ((smallEtaleInclusion B (associatedBigEtaleSite B) rfl (p.obj z).left.1
          (contains_base B (associatedBigEtaleSite B) rfl S hS p z)).obj
          ((smallEtaleBaseChange (associatedBigEtaleSite B)
            (smallEtaleBaseMorphism B (associatedBigEtaleSite B) rfl S hS p φ)).obj V))).left.op
      (F.val.map ((FibredSite.localizationEquivalence B S hS p hp x).inverse.map π).left.op m) :=
    rfl
  rw [hR]
  show (F.val.presheaf.map _ ≫ F.val.presheaf.map φ'.op) m =
    (F.val.presheaf.map _ ≫ F.val.presheaf.map _) m
  rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp, key]

/-- **The inverse image of a quasi-coherent module is an associated module.**  For a
quasi-coherent module `F` on `𝒳` (Stacks 06WG) and an object `x` over a scheme `U`, the inverse
image `x^*F` on `(Sch/U)_fppf` is quasi-coherent (Stacks 06WI), hence of the form `𝓕^a` for a
quasi-coherent `𝒪_U`-module `𝓕` (Stacks 03DX (1)). -/
theorem exists_associatedModule_iso_objectInverseImage
    (F : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS p hp) (x : 𝒳) :
    ∃ 𝓕 : (SheafOfModules.isQuasicoherent ((p.obj x).left.1).ringCatSheaf).FullSubcategory,
      Nonempty ((BigFppfOver.baseAssociatedModule B (p.obj x).left.1 (p.obj x).left.2 .fppf).obj
          𝓕.obj ≅
        FibredSite.objectInverseImageKind B S hS p hp .fppf x F.obj) := by
  obtain ⟨𝓕, ⟨g⟩⟩ := BigFppfOver.quasicoherentIsEssImageAssociatedModule' B
    _ _ _ ((FibredSite.isQuasicoherentOnSite_iff_forall_objectInverseImageKind B S hS p hp .fppf
      F.obj).1 F.property x)
  exact ⟨𝓕, ⟨g⟩⟩

/-- The étale topology on the schemes of `B` is coarser than the fppf topology, as base
topologies of `AlgebraicGeometry.SiteKind`. -/
theorem baseTopology_etale_le_fppf : B.baseTopology .etale ≤ B.baseTopology .fppf :=
  B.baseTopology_le_topology .etale

/-- **`AlgebraicGeometry.Stack.objectInverseImageRestrictIso` on sheaves of modules**: the
restriction `F|_{U_ét}` of Stacks 06WJ is the restriction to the small étale site of `U` of the
inverse image `x^*F` of Stacks 06WI. -/
def objectInverseImageRestrictSheafIso
    (F : SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS p hp .fppf)) (x : 𝒳) :
    (SmallEtale.bigRestrict B (associatedBigEtaleSite B) rfl (p.obj x).left.1
        (contains_base B (associatedBigEtaleSite B) rfl S hS p x) .fppf
        (baseTopology_etale_le_fppf B)).obj
        (FibredSite.objectInverseImageKind B S hS p hp .fppf x F) ≅
      (restrictModuleToSmallEtaleSheafFunctor B (associatedBigEtaleSite B) rfl S hS p hp x).obj
        ((fppfToEtaleSheafOfModules B S hS p hp).obj F) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (objectInverseImageRestrictIso B S hS p hp F x)

section Transpose

attribute [local irreducible] AlgebraicGeometry.smallEtaleBaseChange CategoryTheory.Over.post
  AlgebraicGeometry.Stack.baseStructureSheaf AlgebraicGeometry.Stack.baseRingStructureSheaf

/-- **The transpose of the comparison map of Stacks 06WC on sheaves of modules** along the
adjunction between the sheafified pullback and the pushforward along `ε_a`: on underlying
presheaves it is the comparison of Stacks 06W2, read through the identification of the map
`a_{small}^♯` with the structure map of `ε_a`. -/
theorem sheafifiedPullbackComparisonAdjunction_homEquiv_sheafifiedRestrictComparisonApp_val
    {x z : 𝒳} (φ : z ⟶ x)
    (ℱ : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B))) :
    ((sheafifiedPullbackComparisonAdjunction B (associatedBigEtaleSite B) rfl S hS p hp
        (etaleTopology B) (etaleTopology_le_topology B) φ).homEquiv _ _
        (sheafifiedRestrictComparisonApp B (associatedBigEtaleSite B) rfl S hS p hp φ ℱ)).val =
      restrictModulePushforwardComparison B (associatedBigEtaleSite B) rfl S hS p hp φ
          (etaleTopology B) (etaleTopology_le_topology B) ℱ.val ≫
        (eqToIso (congrArg (fun k => PresheafOfModules.pushforward.{u} k)
          (smallEtaleStructureComparison_eq_smallEtaleStructureMapRing B
            (associatedBigEtaleSite B) rfl S hS p hp (etaleTopology B)
            (etaleTopology_le_topology B) φ))).hom.app
          ((restrictModuleToSmallEtaleSheafFunctor B (associatedBigEtaleSite B) rfl S hS p hp
            z).obj ℱ).val := by
  have key := sheafifiedPullbackComparisonAdjunction_homEquiv_symm_val B (associatedBigEtaleSite B)
    rfl S hS p hp (etaleTopology B) (etaleTopology_le_topology B) φ
    ((restrictModuleToSmallEtaleSheafFunctor B (associatedBigEtaleSite B) rfl S hS p hp x).obj ℱ)
    ((restrictModuleToSmallEtaleSheafFunctor B (associatedBigEtaleSite B) rfl S hS p hp z).obj ℱ)
    (restrictModulePullbackComparison B (associatedBigEtaleSite B) rfl S hS p hp φ
      (etaleTopology B) (etaleTopology_le_topology B) ℱ.val)
  have hadj := restrictModulePullbackComparison_adjunct B (associatedBigEtaleSite B) rfl S hS p
    hp φ (etaleTopology B) (etaleTopology_le_topology B) ℱ.val
  exact key.trans (congrArg (fun k => k ≫ _) hadj)

end Transpose

end AlgebraicGeometry.Stack
