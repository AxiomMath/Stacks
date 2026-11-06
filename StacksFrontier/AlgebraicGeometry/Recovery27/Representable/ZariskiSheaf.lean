module

public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Sites.Representability
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeProjection
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.DescentData
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.ZariskiEssSurj
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.ZariskiGluing
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Support
public import StacksFrontier.AlgebraicGeometry.GrassmannianChart.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFreeDescent.Fpqc
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteTypeQuotient
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.PullbackSkyscraper
public import StacksFrontier.AlgebraicGeometry.Recovery27.Functor
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree
public import StacksFrontier.Topology.Sheaves.Modules.TensorAndDuals.EpiOfConstantRank
public import StacksFrontier.AlgebraicGeometry.Recovery27.Representable.ChartSubfunctors
import StacksCore.Tactic.EgaSgaAttribute
import all StacksFrontier.AlgebraicGeometry.Recovery27.Representable.ChartSubfunctors

/-!
# The Grassmannian functor is a Zariski sheaf

Quotient presentations of the free module of rank `n` glue along open covers: the descent of
quotient maps of free modules along an open cover, and the resulting sheaf property of the
Grassmannian functor `G(k, n)` for the Zariski topology. This is part of the proof that the
Grassmannian functor is representable.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Grassmannian

attribute [local instance 10000] CategoryTheory.CategoryStruct.toQuiver
attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules
attribute [local implicit_reducible] CategoryTheory.Functor.sheafPushforwardContinuous
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local implicit_reducible] SheafOfModules.unit PresheafOfModules.unit
attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules.Hom
attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules.pullback
attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules.pseudofunctor
attribute [local implicit_reducible] CategoryTheory.Bicategory.Adj.forget₁
attribute [local implicit_reducible] CategoryTheory.Pseudofunctor.comp

section

attribute [local instance 10000] CategoryTheory.CategoryStruct.toQuiver

/-- The free module of rank `n` on `S`, as an object of the fibre of the pullback pseudofunctor
over `S`. -/
private noncomputable abbrev freeFibreObj (S : Scheme.{u}) (n : ℕ) :
    AlgebraicGeometry.modulePullbackPseudofunctor.obj (.mk (op S)) :=
  SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin n))

/-- The identifications of the pullbacks of a free module are compatible with the comparison
isomorphism of a composite in the pullback pseudofunctor. -/
private lemma pullbackFreeIso_mapComp' {S T Y : Scheme.{u}}
    (f : T ⟶ S) (g : Y ⟶ T) (a : Y ⟶ S) (ha : g ≫ f = a) (n : ℕ) :
    (AlgebraicGeometry.modulePullbackPseudofunctor.mapComp' f.op.toLoc g.op.toLoc a.op.toLoc
      (by subst a; rfl)).hom.toNatTrans.app (freeFibreObj S n) ≫
      (Scheme.Modules.pullback g).map (pullbackFreeIso f n).hom ≫
        (pullbackFreeIso g n).hom = (pullbackFreeIso a n).hom := by
  subst a
  show (Scheme.Modules.pullbackComp g f).inv.app _ ≫
    (Scheme.Modules.pullback g).map (pullbackFreeIso f n).hom ≫
      (pullbackFreeIso g n).hom = _
  rw [← pullbackFreeIso_comp]
  exact Iso.inv_hom_id_assoc ((Scheme.Modules.pullbackComp g f).app _) _

/-- In any category, a morphism that factors as a split monomorphism followed by `b` composes
with `cd` to `ef`, provided `b ≫ cd` and the splitting followed by `ef` agree. -/
private lemma comp_eq_of_split {𝒞 : Type*} [Category 𝒞] {A R Q T : 𝒞}
    (d : A ⟶ Q) (u : A ⟶ R) (u' : R ⟶ A) (b : R ⟶ Q) (cd : Q ⟶ T) (ef : A ⟶ T) (ι : R ⟶ T)
    (hd : d = u ≫ b) (hu : u ≫ u' = 𝟙 A)
    (h₁ : b ≫ cd = ι) (h₂ : u' ≫ ef = ι) :
    d ≫ cd = ef := by
  rw [hd, Category.assoc, h₁, ← h₂, ← Category.assoc, hu, Category.id_comp]

/-- In any category, the comparison of two factorisations of a morphism through split
isomorphisms. This is the commuting square relating two pullbacks of a quotient map. -/
private lemma comp_eq_of_square {𝒞 : Type*} [Category 𝒞] {A B G X P H Z : 𝒞}
    (α : A ⟶ B) (β : B ⟶ G) (β' : G ⟶ B) (γ : B ⟶ X) (ε : X ⟶ Z)
    (d : A ⟶ P) (δ : P ⟶ H) (δ' : H ⟶ G) (δ'' : G ⟶ H) (ζ : H ⟶ Z)
    (mg : A ⟶ X) (mh : P ⟶ Z)
    (hmg : mg = α ≫ γ) (hmh : mh = δ ≫ ζ)
    (hβ : β ≫ β' = 𝟙 B) (hδ : δ' ≫ δ'' = 𝟙 H)
    (he : (β' ≫ γ) ≫ ε = δ'' ≫ ζ)
    (hd : d ≫ δ ≫ δ' = α ≫ β) :
    mg ≫ ε = d ≫ mh := by
  rw [hmg, hmh]
  calc (α ≫ γ) ≫ ε
      = (α ≫ (β ≫ β') ≫ γ) ≫ ε := by rw [hβ, Category.id_comp]
    _ = (α ≫ β) ≫ (β' ≫ γ) ≫ ε := by simp only [Category.assoc]
    _ = (α ≫ β) ≫ δ'' ≫ ζ := by rw [he]
    _ = (d ≫ δ ≫ δ') ≫ δ'' ≫ ζ := by rw [hd]
    _ = d ≫ δ ≫ (δ' ≫ δ'') ≫ ζ := by simp only [Category.assoc]
    _ = d ≫ δ ≫ ζ := by rw [hδ, Category.id_comp]

/-- Through the identifications of the pullbacks of a free module, the canonical descent datum
of the free module has the identity transition morphisms. -/
private lemma descentFree_hom {S : Scheme.{u}} (n : ℕ) (𝒰 : S.OpenCover)
    {Y : Scheme.{u}} (a : Y ⟶ S) {i j : 𝒰.I₀}
    (g : Y ⟶ 𝒰.X i) (h : Y ⟶ 𝒰.X j)
    (hg : g ≫ 𝒰.f i = a) (hh : h ≫ 𝒰.f j = a) :
    ((AlgebraicGeometry.modulePullbackPseudofunctor.toDescentData 𝒰.f).obj
      (freeFibreObj S n)).hom a g h hg hh ≫
        (Scheme.Modules.pullback h).map (pullbackFreeIso (𝒰.f j) n).hom ≫
          (pullbackFreeIso h n).hom =
      (Scheme.Modules.pullback g).map (pullbackFreeIso (𝒰.f i) n).hom ≫
        (pullbackFreeIso g n).hom := by
  have hu : (AlgebraicGeometry.modulePullbackPseudofunctor.mapComp' (𝒰.f i).op.toLoc g.op.toLoc
        a.op.toLoc (by grind)).inv.toNatTrans.app (freeFibreObj S n) ≫
      (AlgebraicGeometry.modulePullbackPseudofunctor.mapComp' (𝒰.f i).op.toLoc g.op.toLoc
        a.op.toLoc (by grind)).hom.toNatTrans.app (freeFibreObj S n) = 𝟙 _ := by
    rw [← Cat.Hom₂.comp_app, Iso.inv_hom_id, Cat.Hom₂.id_app]
  exact comp_eq_of_split _ _ _ _ _ _ _ rfl hu
    (pullbackFreeIso_mapComp' (𝒰.f j) h a hh n)
    (pullbackFreeIso_mapComp' (𝒰.f i) g a hg n)

end

section Descent

open Pseudofunctor.LocallyDiscreteOpToCat

universe v₀ u₀ v₁ u₁ w₀

variable {C : Type u₀} [Category.{v₀} C]
  {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v₁, u₁}}

/-- A square of transition morphisms commuting over `Y` still commutes after pulling back along
a morphism into `Y`. -/
private lemma pullHom_comm
    {X₁ X₂ Y Y' : C} {M₁ N₁ : F.obj (.mk (op X₁))}
    {M₂ N₂ : F.obj (.mk (op X₂))} (p₁ : M₁ ⟶ N₁) (p₂ : M₂ ⟶ N₂)
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (a : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶
      (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (b : (F.map f₁.op.toLoc).toFunctor.obj N₁ ⟶
      (F.map f₂.op.toLoc).toFunctor.obj N₂)
    (h : (F.map f₁.op.toLoc).toFunctor.map p₁ ≫ b =
      a ≫ (F.map f₂.op.toLoc).toFunctor.map p₂)
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    (F.map gf₁.op.toLoc).toFunctor.map p₁ ≫ pullHom b g gf₁ gf₂ hgf₁ hgf₂ =
      pullHom a g gf₁ gf₂ hgf₁ hgf₂ ≫ (F.map gf₂.op.toLoc).toFunctor.map p₂ := by
  dsimp only [pullHom]
  rw [F.mapComp'_hom_naturality_assoc, ← Functor.map_comp_assoc, h,
    Functor.map_comp_assoc]
  simp only [Category.assoc, F.mapComp'_inv_naturality]

/-- A descent datum of quotients of a given one, built from a family of transition morphisms
for the quotients compatible with those of the given datum. -/
private noncomputable def quotientDescentData
    {I : Type w₀} {S : C} {X : I → C} {f : ∀ i, X i ⟶ S}
    (D : F.DescentData f) (Q : ∀ i, F.obj (.mk (op (X i))))
    (p : ∀ i, D.obj i ⟶ Q i)
    (hp : ∀ (Y : C) (i : I) (g : Y ⟶ X i),
      Epi ((F.map g.op.toLoc).toFunctor.map (p i)))
    (t : ∀ (Y : C) (q : Y ⟶ S) (i₁ i₂ : I)
      (g₁ : Y ⟶ X i₁) (g₂ : Y ⟶ X i₂),
      g₁ ≫ f i₁ = q → g₂ ≫ f i₂ = q →
      ((F.map g₁.op.toLoc).toFunctor.obj (Q i₁) ⟶
        (F.map g₂.op.toLoc).toFunctor.obj (Q i₂)))
    (ht : ∀ (Y : C) (q : Y ⟶ S) (i₁ i₂ : I)
      (g₁ : Y ⟶ X i₁) (g₂ : Y ⟶ X i₂)
      (h₁ : g₁ ≫ f i₁ = q) (h₂ : g₂ ≫ f i₂ = q),
      (F.map g₁.op.toLoc).toFunctor.map (p i₁) ≫ t Y q i₁ i₂ g₁ g₂ h₁ h₂ =
        D.hom q g₁ g₂ h₁ h₂ ≫ (F.map g₂.op.toLoc).toFunctor.map (p i₂)) :
    F.DescentData f := by
  refine
    { obj := Q
      hom := fun Y q i₁ i₂ g₁ g₂ h₁ h₂ => t Y q i₁ i₂ g₁ g₂ h₁ h₂
      pullHom_hom := ?_
      hom_self := ?_
      hom_comp := ?_ }
  · intro Y' Y g q q' hq i₁ i₂ g₁ g₂ h₁ h₂ gg₁ gg₂ hgg₁ hgg₂
    let := hp Y' i₁ gg₁
    apply (cancel_epi ((F.map gg₁.op.toLoc).toFunctor.map (p i₁))).1
    rw [ht]
    rw [pullHom_comm (p i₁) (p i₂) _ _ (ht Y q i₁ i₂ g₁ g₂ h₁ h₂)
      g gg₁ gg₂ hgg₁ hgg₂,
      D.pullHom_hom g q q' hq g₁ g₂ h₁ h₂ gg₁ gg₂ hgg₁ hgg₂]
  · intro Y q i g hg
    let := hp Y i g
    apply (cancel_epi ((F.map g.op.toLoc).toFunctor.map (p i))).1
    rw [ht, D.hom_self q g hg, Category.id_comp, Category.comp_id]
  · intro Y q i₁ i₂ i₃ g₁ g₂ g₃ h₁ h₂ h₃
    let := hp Y i₁ g₁
    apply (cancel_epi ((F.map g₁.op.toLoc).toFunctor.map (p i₁))).1
    rw [← Category.assoc, ht, Category.assoc, ht, ← Category.assoc, D.hom_comp, ht]

/-- Two quotients of a descent datum by epimorphisms are isomorphic as descent data once they
are isomorphic componentwise compatibly with the quotient maps. -/
private noncomputable def descentIsoOfEpi
    {I : Type w₀} {S : C} {X : I → C} {f : ∀ i, X i ⟶ S}
    {D D₁ D₂ : F.DescentData f} (p₁ : D ⟶ D₁) (p₂ : D ⟶ D₂)
    (hp : ∀ (Y : C) (i : I) (g : Y ⟶ X i),
      Epi ((F.map g.op.toLoc).toFunctor.map (p₁.hom i)))
    (e : ∀ i, D₁.obj i ≅ D₂.obj i) (he : ∀ i, p₁.hom i ≫ (e i).hom = p₂.hom i) :
    D₁ ≅ D₂ := by
  refine Pseudofunctor.DescentData.isoMk e ?_
  intro Y q i₁ i₂ g₁ g₂ h₁ h₂
  let := hp Y i₁ g₁
  apply (cancel_epi ((F.map g₁.op.toLoc).toFunctor.map (p₁.hom i₁))).1
  rw [← Category.assoc, ← Functor.map_comp, he i₁, p₂.comm q g₁ g₂ h₁ h₂]
  rw [← Category.assoc _ (D₁.hom q g₁ g₂ h₁ h₂), p₁.comm q g₁ g₂ h₁ h₂,
    Category.assoc, ← Functor.map_comp, he i₂]

end Descent

/-- A morphism from the canonical descent datum of a quasi-coherent module to a quasi-coherent
descent datum comes from a morphism of modules on the base. -/
private lemma exists_quasicoherent_descent_morphism {S : Scheme.{u}}
    (𝒰 : S.OpenCover)
    (M : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory)
    (D : AlgebraicGeometry.QuasicoherentDescentData 𝒰.f)
    (φ : (AlgebraicGeometry.canonicalDescentFunctor 𝒰.f).obj M ⟶ D) :
    ∃ (N : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory)
      (p : M ⟶ N) (e : (AlgebraicGeometry.canonicalDescentFunctor 𝒰.f).obj N ≅ D),
      (AlgebraicGeometry.canonicalDescentFunctor 𝒰.f).map p ≫ e.hom = φ := by
  obtain ⟨N, ⟨e⟩⟩ :=
    Stacks.Descent.isEffective_openCover 𝒰 D
  let ff :=
    (Stacks.Descent.nonempty_fullyFaithful_canonicalDescentFunctor_openCover 𝒰).some
  refine ⟨N, ff.preimage (φ ≫ e.inv), e, ?_⟩
  rw [ff.map_preimage]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The quotient map of a pulled-back presentation. -/
private lemma pullbackPresentation_map {S T : Scheme.{u}} {k n : ℕ} (f : T ⟶ S)
    (q : QuotientPresentation S k n) :
    (pullbackPresentation f q).map =
      (pullbackFreeIso f n).inv ≫ (Scheme.Modules.pullback f).map q.map := rfl

/-- The identification of the pullback of a free module with the free module is surjective. -/
private lemma epi_pullbackFreeIso_hom {S T : Scheme.{u}} (f : T ⟶ S) (n : ℕ) :
    Epi (pullbackFreeIso f n).hom :=
  inferInstance

/-- Two presentations on the base whose pullbacks along `f` are isomorphic have isomorphic
pulled-back targets, compatibly with the pulled-back quotient maps. -/
private lemma exists_pullbackTargetIso {S T : Scheme.{u}} {k n : ℕ} (f : T ⟶ S)
    (q q' : QuotientPresentation S k n)
    (hiso : (pullbackPresentation f q).Isomorphic (pullbackPresentation f q')) :
    ∃ e : (Scheme.Modules.pullback f).obj q.target ≅
        (Scheme.Modules.pullback f).obj q'.target,
      (Scheme.Modules.pullback f).map q.map ≫ e.hom =
        (Scheme.Modules.pullback f).map q'.map := by
  obtain ⟨e, he⟩ := hiso
  rw [pullbackPresentation_map, pullbackPresentation_map] at he
  refine ⟨e, ?_⟩
  refine (cancel_epi (pullbackFreeIso f n).inv).1 ?_
  exact (Category.assoc _ _ _).symm.trans he

/-- The transition isomorphism joining two agreeing pullbacks of a family of quotient
presentations commutes with the quotient maps of the canonical descent datum of the free
module. -/
private lemma exists_descentTransition {S : Scheme.{u}} {k n : ℕ} (𝒰 : S.OpenCover)
    (q : ∀ i, QuotientPresentation (𝒰.X i) k n) {Y : Scheme.{u}} (a : Y ⟶ S) (i j : 𝒰.I₀)
    (g : Y ⟶ 𝒰.X i) (h' : Y ⟶ 𝒰.X j)
    (hg : g ≫ 𝒰.f i = a) (hh : h' ≫ 𝒰.f j = a)
    (hiso : (pullbackPresentation g (q i)).Isomorphic (pullbackPresentation h' (q j))) :
    ∃ t : (Scheme.Modules.pullback g).obj (q i).target ⟶
        (Scheme.Modules.pullback h').obj (q j).target,
      (Scheme.Modules.pullback g).map ((pullbackFreeIso (𝒰.f i) n).hom ≫ (q i).map) ≫ t =
        ((AlgebraicGeometry.modulePullbackPseudofunctor.toDescentData 𝒰.f).obj
            (freeFibreObj S n)).hom a g h' hg hh ≫
          (Scheme.Modules.pullback h').map
            ((pullbackFreeIso (𝒰.f j) n).hom ≫ (q j).map) := by
  obtain ⟨e, he⟩ := hiso
  rw [pullbackPresentation_map, pullbackPresentation_map] at he
  refine ⟨e.hom, ?_⟩
  exact comp_eq_of_square
    ((Scheme.Modules.pullback g).map (pullbackFreeIso (𝒰.f i) n).hom)
    (pullbackFreeIso g n).hom (pullbackFreeIso g n).inv
    ((Scheme.Modules.pullback g).map (q i).map) e.hom
    (((AlgebraicGeometry.modulePullbackPseudofunctor.toDescentData 𝒰.f).obj
      (freeFibreObj S n)).hom a g h' hg hh)
    ((Scheme.Modules.pullback h').map (pullbackFreeIso (𝒰.f j) n).hom)
    (pullbackFreeIso h' n).hom (pullbackFreeIso h' n).inv
    ((Scheme.Modules.pullback h').map (q j).map) _ _
    ((Scheme.Modules.pullback g).map_comp _ _)
    ((Scheme.Modules.pullback h').map_comp _ _)
    (pullbackFreeIso g n).hom_inv_id (pullbackFreeIso h' n).hom_inv_id
    he (descentFree_hom n 𝒰 a g h' hg hh)

/-- The target of a quotient presentation is quasi-coherent. -/
private lemma isQuasicoherent_target {X : Scheme.{u}} {k n : ℕ}
    (q : QuotientPresentation X k n) : q.target.IsQuasicoherent := by
  let := q.finiteLocallyFree
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
    q.target (n - k)
  exact inferInstanceAs q.target.IsQuasicoherent

/-- The componentwise isomorphism underlying an isomorphism of quasi-coherent descent data. -/
private noncomputable def descentDataIsoApp {S : Scheme.{u}} {𝒰 : S.OpenCover}
    {D₁ D₂ : AlgebraicGeometry.QuasicoherentDescentData 𝒰.f} (e : D₁ ≅ D₂) (i : 𝒰.I₀) :
    D₁.obj.obj i ≅ D₂.obj.obj i where
  hom := e.hom.hom.hom i
  inv := e.inv.hom.hom i
  hom_inv_id := congrArg (fun t => t.hom.hom i) e.hom_inv_id
  inv_hom_id := congrArg (fun t => t.hom.hom i) e.inv_hom_id

/-- The free module of finite rank is quasi-coherent. -/
private lemma isQuasicoherent_free (S : Scheme.{u}) (n : ℕ) :
    (SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin n))).IsQuasicoherent :=
  inferInstance

/-- A choice of transition morphisms between the pullbacks of a family of quotient
presentations, compatible with the canonical descent datum of the free module. -/
private lemma exists_descentTransitionFamily {S : Scheme.{u}} {k n : ℕ} (𝒰 : S.OpenCover)
    (q : ∀ i, QuotientPresentation (𝒰.X i) k n)
    (h : ∀ (Y : Scheme.{u}) (a : Y ⟶ S) (i j : 𝒰.I₀)
      (g : Y ⟶ 𝒰.X i) (h : Y ⟶ 𝒰.X j),
      g ≫ 𝒰.f i = a → h ≫ 𝒰.f j = a →
      (pullbackPresentation g (q i)).Isomorphic
        (pullbackPresentation h (q j))) :
    ∃ t : ∀ (Y : Scheme.{u}) (a : Y ⟶ S) (i j : 𝒰.I₀) (g : Y ⟶ 𝒰.X i) (h' : Y ⟶ 𝒰.X j),
        g ≫ 𝒰.f i = a → h' ≫ 𝒰.f j = a →
        ((Scheme.Modules.pullback g).obj (q i).target ⟶
          (Scheme.Modules.pullback h').obj (q j).target),
      ∀ (Y : Scheme.{u}) (a : Y ⟶ S) (i j : 𝒰.I₀) (g : Y ⟶ 𝒰.X i) (h' : Y ⟶ 𝒰.X j)
        (hg : g ≫ 𝒰.f i = a) (hh : h' ≫ 𝒰.f j = a),
        (Scheme.Modules.pullback g).map ((pullbackFreeIso (𝒰.f i) n).hom ≫ (q i).map) ≫
            t Y a i j g h' hg hh =
          ((AlgebraicGeometry.modulePullbackPseudofunctor.toDescentData 𝒰.f).obj
              (freeFibreObj S n)).hom a g h' hg hh ≫
            (Scheme.Modules.pullback h').map
              ((pullbackFreeIso (𝒰.f j) n).hom ≫ (q j).map) := by
  choose t ht using fun (Y : Scheme.{u}) (a : Y ⟶ S) (i j : 𝒰.I₀) (g : Y ⟶ 𝒰.X i)
      (h' : Y ⟶ 𝒰.X j) (hg : g ≫ 𝒰.f i = a) (hh : h' ≫ 𝒰.f j = a) =>
    exists_descentTransition 𝒰 q a i j g h' hg hh (h Y a i j g h' hg hh)
  exact ⟨t, ht⟩

/-- A morphism of descent data from the canonical datum of the free module to a datum with
quasi-coherent components is induced, componentwise, by a quasi-coherent quotient of the free
module on the base. -/
private lemma exists_descended_quotientMap {S : Scheme.{u}} {n : ℕ} (𝒰 : S.OpenCover)
    (E : AlgebraicGeometry.modulePullbackPseudofunctor.DescentData 𝒰.f)
    (hE : ∀ i, (E.obj i).IsQuasicoherent)
    (φ : (AlgebraicGeometry.modulePullbackPseudofunctor.toDescentData 𝒰.f).obj
        (freeFibreObj S n) ⟶ E) :
    ∃ (N : S.Modules) (_ : N.IsQuasicoherent)
      (π : SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin n)) ⟶ N)
      (e : ∀ i, (Scheme.Modules.pullback (𝒰.f i)).obj N ≅ E.obj i),
      ∀ i, (Scheme.Modules.pullback (𝒰.f i)).map π ≫ (e i).hom = φ.hom i := by
  obtain ⟨N, π, e, he⟩ := exists_quasicoherent_descent_morphism 𝒰
    ⟨SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin n)), isQuasicoherent_free S n⟩
    ⟨E, hE⟩ (ObjectProperty.homMk φ)
  exact ⟨N.obj, N.property, π.hom, fun i => descentDataIsoApp e i,
    fun i => congrArg (fun t => t.hom.hom i) he⟩

section

attribute [local instance 10000] CategoryTheory.CategoryStruct.toQuiver

/-- Quotient presentations on the members of an open cover whose pullbacks agree glue to a
quasi-coherent quotient of the free module of rank `n` on the base. -/
private lemma exists_glued_quotientMap {S : Scheme.{u}} {k n : ℕ}
    (𝒰 : S.OpenCover) (q : ∀ i, QuotientPresentation (𝒰.X i) k n)
    (h : ∀ (Y : Scheme.{u}) (a : Y ⟶ S) (i j : 𝒰.I₀)
      (g : Y ⟶ 𝒰.X i) (h : Y ⟶ 𝒰.X j),
      g ≫ 𝒰.f i = a → h ≫ 𝒰.f j = a →
      (pullbackPresentation g (q i)).Isomorphic
        (pullbackPresentation h (q j))) :
    ∃ (N : S.Modules) (_ : N.IsQuasicoherent)
      (p : SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin n)) ⟶ N)
      (e : ∀ i, (Scheme.Modules.pullback (𝒰.f i)).obj N ≅ (q i).target),
      ∀ i, (Scheme.Modules.pullback (𝒰.f i)).map p ≫ (e i).hom =
        (pullbackFreeIso (𝒰.f i) n).hom ≫ (q i).map := by
  obtain ⟨t, ht⟩ := exists_descentTransitionFamily 𝒰 q h
  let A : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory :=
    ⟨SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin n)), isQuasicoherent_free S n⟩
  let D := (AlgebraicGeometry.modulePullbackPseudofunctor.toDescentData 𝒰.f).obj
    (freeFibreObj S n)
  let Q := fun i => (q i).target
  let p : ∀ i, D.obj i ⟶ Q i :=
    fun i => (pullbackFreeIso (𝒰.f i) n).hom ≫ (q i).map
  have hp (Y : Scheme.{u}) (i : 𝒰.I₀) (g : Y ⟶ 𝒰.X i) :
      Epi ((Scheme.Modules.pullback g).map (p i)) :=
    pullback_preserves_epi g _
      (@epi_comp _ _ _ _ _ _ (epi_pullbackFreeIso_hom (𝒰.f i) n) _ (q i).map_epi)
  exact exists_descended_quotientMap 𝒰
    (quotientDescentData D Q p hp (fun Y a i j g h' hg hh => t Y a i j g h' hg hh)
      (fun Y a i j g h' hg hh => ht Y a i j g h' hg hh))
    (fun i => isQuasicoherent_target (q i))
    { hom := p
      comm := fun Y a i j g h' hg hh => ht Y a i j g h' hg hh }

/-- Two presentations whose pullbacks to the members of an open cover are isomorphic are
isomorphic. -/
private lemma quotientPresentation_isomorphic_of_local {S : Scheme.{u}} {k n : ℕ}
    (𝒰 : S.OpenCover) (q q' : QuotientPresentation S k n)
    (h : ∀ i, (pullbackPresentation (𝒰.f i) q).Isomorphic
      (pullbackPresentation (𝒰.f i) q')) : q.Isomorphic q' := by
  let := q.map_epi
  let := q'.map_epi
  let := q.finiteLocallyFree
  let := q'.finiteLocallyFree
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
    q.target (n - k)
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
    q'.target (n - k)
  let A : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory :=
    ⟨SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin n)), inferInstance⟩
  let B : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory :=
    ⟨q.target, inferInstance⟩
  let B' : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory :=
    ⟨q'.target, inferInstance⟩
  let p : A ⟶ B := ObjectProperty.homMk q.map
  let p' : A ⟶ B' := ObjectProperty.homMk q'.map
  let Φ := AlgebraicGeometry.canonicalDescentFunctor 𝒰.f
  choose e he using fun i => exists_pullbackTargetIso (𝒰.f i) q q' (h i)
  let ed : (Φ.obj B).obj ≅ (Φ.obj B').obj :=
    descentIsoOfEpi (Φ.map p).hom (Φ.map p').hom
      (fun Y i g => pullback_preserves_epi g _
        (pullback_preserves_epi (𝒰.f i) _ q.map_epi)) e he
  let ed' : Φ.obj B ≅ Φ.obj B' := ObjectProperty.isoMk _ ed
  let ff :=
    (Stacks.Descent.nonempty_fullyFaithful_canonicalDescentFunctor_openCover 𝒰).some
  let eg := ff.preimageIso ed'
  have hg : p ≫ eg.hom = p' := by
    apply ff.map_injective
    rw [Functor.map_comp]
    show Φ.map p ≫ Φ.map (ff.preimage ed'.hom) = Φ.map p'
    rw [ff.map_preimage]
    apply ObjectProperty.hom_ext
    apply Pseudofunctor.DescentData.hom_ext
    intro i
    exact he i
  exact ⟨(ObjectProperty.ι (SheafOfModules.isQuasicoherent S.ringCatSheaf)).mapIso eg,
    congrArg (fun t => t.hom) hg⟩

end

/-- Two points of `G(k, n)` agreeing on the members of an open cover are equal. -/
private lemma points_eq_of_openCover {S : Scheme.{u}} (k n : ℕ)
    (𝒰 : S.OpenCover) (x y : (functor.{u} k n).obj (op S))
    (h : ∀ i, (functor.{u} k n).map (𝒰.f i).op x =
      (functor.{u} k n).map (𝒰.f i).op y) : x = y := by
  let E := (functorData.{u} k n).objEquiv S
  obtain ⟨q, hq⟩ := Quotient.exists_rep (E x)
  obtain ⟨q', hq'⟩ := Quotient.exists_rep (E y)
  have hx : x = E.symm ⟦q⟧ := E.injective (by simpa using hq.symm)
  have hy : y = E.symm ⟦q'⟧ := E.injective (by simpa using hq'.symm)
  apply E.injective
  rw [← hq, ← hq']
  apply Quotient.sound
  apply Relation.EqvGen.rel
  apply quotientPresentation_isomorphic_of_local 𝒰 q q'
  intro i
  apply quotientPresentation_isomorphic_of_eq
  have hi := congrArg ((functorData.{u} k n).objEquiv (𝒰.X i)) (h i)
  rw [hx, hy] at hi
  rw [points_map_of_isPullback (𝒰.f i) q _
      (pullbackPresentation_isPullback (𝒰.f i) q),
    points_map_of_isPullback (𝒰.f i) q' _
      (pullbackPresentation_isPullback (𝒰.f i) q')] at hi
  exact hi

/-- An equivalence of index types induces an isomorphism of the free modules on them. -/
private noncomputable def freeEquivIso {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
    [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {I I' : Type u} (e : I ≃ I') :
    SheafOfModules.free (R := R) I ≅ SheafOfModules.free I' :=
  (SheafOfModules.freeFunctor (R := R)).mapIso (Equiv.toIso e)

/-- A module that is finite locally free of rank `r` is free of rank `r` on a neighbourhood of
every point. -/
private lemma exists_free_pullback_of_rank {S : Scheme.{u}} (M : S.Modules) (r : ℕ)
    (h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r) (x : S) :
    ∃ U : S.Opens, x ∈ U ∧ Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅
      SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin r))) := by
  obtain ⟨q, hq, hr⟩ := h.exists_isFiniteLocallyFreeOfRankData
  have hx : x ∈ ⨆ i, q.X i := by
    rw [(Opens.coversTop_iff S q.X).mp q.coversTop]
    trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  let U : S.Opens := q.X i
  let E := Scheme.Modules.overEquiv U
  let : IsIso (q.generators i).π := hq.isIso i
  let e := asIso (q.generators i).π
  let eFree := SheafOfModules.mapFreeIso E.functor (q.generators i).I (Iso.refl _)
  let er := freeEquivIso U.toScheme.ringCatSheaf ((hr i).some.trans Equiv.ulift.symm)
  refine ⟨U, hi, ⟨?_⟩⟩
  exact ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M).symm ≪≫
    ((Scheme.Modules.overFunctorEquiv U).app M).symm ≪≫
    (E.functor.mapIso e).symm ≪≫ eFree.symm ≪≫ er

/-- A module that is free of rank `r` on a neighbourhood of every point is finite locally free
of rank `r`. -/
private lemma rank_of_free_pullback {S : Scheme.{u}} (M : S.Modules) (r : ℕ)
    (h : ∀ x : S, ∃ U : S.Opens, x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅
        SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin r)))) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r := by
  classical
  choose U hx e using h
  let eOver (x : S) : SheafOfModules.free (R := S.ringCatSheaf.over (U x))
      (ULift.{u} (Fin r)) ≅ M.over (U x) := by
    let E := Scheme.Modules.overEquiv (U x)
    let t := ((Scheme.Modules.overFunctorEquiv (U x)).app M) ≪≫
      ((Scheme.Modules.restrictFunctorIsoPullback (U x).ι).app M) ≪≫ (e x).some
    exact SheafOfModules.mapFreeIso E.inverse (ULift.{u} (Fin r))
      (Opens.sheafOfModulesEquivOverInverseUnit (U x) S.ringCatSheaf).symm ≪≫
      E.inverse.mapIso t.symm ≪≫ (E.unitIso.app _).symm
  let q : M.LocalGeneratorsData.{u} := {
    I := S
    X := U
    coversTop := (Opens.coversTop_iff S U).mpr <| IsOpenCover.mk <| by
      apply top_unique
      intro x _
      exact Opens.mem_iSup.mpr ⟨x, hx x⟩
    generators x := (SheafOfModules.free.generatingSections (ULift.{u} (Fin r))).ofEpi
      (eOver x).hom }
  constructor
  refine ⟨q, ?_, ?_⟩
  · constructor
    intro x
    show IsIso (((SheafOfModules.free.generatingSections (ULift.{u} (Fin r))).ofEpi
      (eOver x).hom).π)
    rw [SheafOfModules.GeneratingSections.ofEpi_π]
    have h1 : IsIso (SheafOfModules.free.generatingSections
        (R := S.ringCatSheaf.over (U x)) (ULift.{u} (Fin r))).π := inferInstance
    have h2 : IsIso (eOver x).hom :=
      ⟨(eOver x).inv, (eOver x).hom_inv_id, (eOver x).inv_hom_id⟩
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 h2
  · intro x
    exact ⟨Equiv.ulift⟩

/-- Finite local freeness of rank `r` is local on an open cover. -/
private lemma rank_of_openCover {S : Scheme.{u}} (M : S.Modules) (r : ℕ)
    (𝒰 : S.OpenCover)
    (h : ∀ i, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (𝒰.f i)).obj M) r) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r := by
  apply rank_of_free_pullback
  intro x
  obtain ⟨i, y, hy⟩ := 𝒰.exists_eq x
  obtain ⟨V, hyV, ⟨eV⟩⟩ := exists_free_pullback_of_rank _ r (h i) y
  let f := V.ι ≫ 𝒰.f i
  let e : (Scheme.Modules.pullback f).obj M ≅
      SheafOfModules.free (R := V.toScheme.ringCatSheaf) (ULift.{u} (Fin r)) :=
    ((Scheme.Modules.pullbackComp V.ι (𝒰.f i)).app M).symm ≪≫ eV
  refine ⟨f.opensRange, ⟨⟨y, hyV⟩, hy⟩, ⟨?_⟩⟩
  exact ((Scheme.Modules.pullbackCongr f.isoOpensRange_inv_comp).app M).symm ≪≫
    ((Scheme.Modules.pullbackComp f.isoOpensRange.inv f).app M).symm ≪≫
    (Scheme.Modules.pullback f.isoOpensRange.inv).mapIso e ≪≫
    pullbackFreeIso f.isoOpensRange.inv r

/-- A morphism of sheaves of modules that becomes surjective over each member of a cover by
opens is surjective. -/
private lemma epi_of_overFunctor_openCover {X : TopCat.{u}}
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ U, HasWeakSheafify ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u}]
    [∀ U, ((Opens.grothendieckTopology X).over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (F G : SheafOfModules.{u} R) (f : F ⟶ G)
    {J : Type*} (U : J → Opens X) (hU : IsOpenCover U)
    (h_epi : ∀ j, Epi ((SheafOfModules.overFunctor R (U j)).map f)) : Epi f := by
  refine ⟨fun {Z} g k hgf => ?_⟩
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  ext s
  apply TopCat.Presheaf.section_ext ((SheafOfModules.toSheaf R).obj Z) V.unop
  intro x hx
  obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp (hU.iSup_set_eq_univ ▸ Set.mem_univ x)
  let W : Opens X := V.unop ⊓ U j
  have hxW : x ∈ W := ⟨hx, hxj⟩
  have hWV : W ≤ V.unop := inf_le_left
  have hWU : W ≤ U j := inf_le_right
  let sW := (G.val.map (homOfLE hWV).op) s
  have hgfU :
      (SheafOfModules.overFunctor R (U j)).map f ≫
          (SheafOfModules.overFunctor R (U j)).map g =
        (SheafOfModules.overFunctor R (U j)).map f ≫
          (SheafOfModules.overFunctor R (U j)).map k := by
    simpa only [Functor.map_comp] using congrArg
      (fun q => (SheafOfModules.overFunctor R (U j)).map q) hgf
  have : Epi ((SheafOfModules.overFunctor R (U j)).map f) := h_epi j
  have hgk : (SheafOfModules.overFunctor R (U j)).map g =
      (SheafOfModules.overFunctor R (U j)).map k :=
    (cancel_epi ((SheafOfModules.overFunctor R (U j)).map f)).mp hgfU
  have hlocal :
      (ConcreteCategory.hom (g.val.app (op W))) sW =
        (ConcreteCategory.hom (k.val.app (op W))) sW := by
    have hcomp := congrArg
      (fun q => q.val.app (op (Over.mk (homOfLE hWU)))) hgk
    have happ := congrArg (fun q => (ConcreteCategory.hom q) sW) hcomp
    change (ConcreteCategory.hom (g.val.app (op W))) sW =
      (ConcreteCategory.hom (k.val.app (op W))) sW at happ
    exact happ
  have hrestr :
      (ConcreteCategory.hom (Z.val.map (homOfLE hWV).op))
          ((ConcreteCategory.hom (g.val.app (op V.unop))) s) =
        (ConcreteCategory.hom (Z.val.map (homOfLE hWV).op))
          ((ConcreteCategory.hom (k.val.app (op V.unop))) s) := by
    have hgNat := PresheafOfModules.naturality_apply g.val
      (homOfLE hWV).op s
    have hkNat := PresheafOfModules.naturality_apply k.val
      (homOfLE hWV).op s
    dsimp [sW] at hlocal
    rw [← hgNat, hlocal, hkNat]
  show (TopCat.Presheaf.germ Z.val.presheaf V.unop x hx).hom
      ((ConcreteCategory.hom (g.val.app (op V.unop))) s) =
      (TopCat.Presheaf.germ Z.val.presheaf V.unop x hx).hom
      ((ConcreteCategory.hom (k.val.app (op V.unop))) s)
  rw [← TopCat.Presheaf.germ_res_apply Z.val.presheaf
      (homOfLE hWV) x hxW ((ConcreteCategory.hom (g.val.app (op V.unop))) s)]
  rw [← TopCat.Presheaf.germ_res_apply Z.val.presheaf
      (homOfLE hWV) x hxW ((ConcreteCategory.hom (k.val.app (op V.unop))) s)]
  exact congrArg (fun z => (TopCat.Presheaf.germ Z.val.presheaf W x hxW).hom z) hrestr

/-- A morphism is surjective if its image under a functor naturally isomorphic to another functor
is, where the second functor preserves it. -/
private lemma epi_map_of_natIso {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (t : F ≅ G) {X Y : C} (f : X ⟶ Y) (h : Epi (G.map f)) : Epi (F.map f) := by
  refine (epi_comp_iso_iff _ (t.app Y)).mp ?_
  rw [Iso.app_hom, t.hom.naturality f]
  infer_instance

/-- A morphism of modules whose pullbacks to the members of a cover by opens are surjective is
surjective. -/
private lemma epi_of_pullback_opensCover {S : Scheme.{u}}
    {J : Type*} (U : J → S.Opens) (hU : IsOpenCover U)
    {M N : S.Modules} (f : M ⟶ N)
    (h : ∀ j, Epi ((Scheme.Modules.pullback (U j).ι).map f)) : Epi f := by
  apply epi_of_overFunctor_openCover S.ringCatSheaf M N f U hU
  intro j
  let E := Scheme.Modules.overEquiv (U j)
  exact E.functor.epi_of_epi_map <| epi_map_of_natIso
    (Scheme.Modules.overFunctorEquiv (U j)) f <| epi_map_of_natIso
    (Scheme.Modules.restrictFunctorIsoPullback (U j).ι) f (h j)

/-- A family of opens covering a scheme, viewed as an open cover. -/
private noncomputable def openCoverOfOpens {S : Scheme.{u}}
    {J : Type*} (U : J → S.Opens) (hU : IsOpenCover U) : S.OpenCover := by
  refine
    { I₀ := J
      X := fun j => (U j : Scheme)
      f := fun j => (U j).ι
      mem₀ := ?_ }
  rw [Scheme.presieve₀_mem_precoverage_iff]
  refine ⟨?_, inferInstance⟩
  intro x
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hU.iSup_set_eq_univ ▸ Set.mem_univ x)
  exact ⟨j, ⟨x, hj⟩, rfl⟩

/-- A glued quotient map is surjective after pullback to each member of the cover. -/
private lemma glued_quotientMap_pullback_epi
    {S : Scheme.{u}} {k n : ℕ}
    (𝒰 : S.OpenCover) (q : ∀ i, QuotientPresentation (𝒰.X i) k n)
    (N : S.Modules)
    (p : SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin n)) ⟶ N)
    (e : ∀ i, (Scheme.Modules.pullback (𝒰.f i)).obj N ≅ (q i).target)
    (he : ∀ i, (Scheme.Modules.pullback (𝒰.f i)).map p ≫ (e i).hom =
      (pullbackFreeIso (𝒰.f i) n).hom ≫ (q i).map) :
    ∀ i, Epi ((Scheme.Modules.pullback (𝒰.f i)).map p) := by
  intro i
  have hi : Epi ((Scheme.Modules.pullback (𝒰.f i)).map p ≫ (e i).hom) := by
    rw [he i]
    let : Epi (q i).map := (q i).map_epi
    infer_instance
  exact (epi_comp_iso_iff _ (e i)).mp hi

/-- A morphism of modules whose pullbacks along the members of an open cover are surjective is
surjective. -/
private lemma epi_of_pullback_openCover {S : Scheme.{u}}
    (𝒰 : S.OpenCover) {M N : S.Modules} (p : M ⟶ N)
    (h : ∀ i, Epi ((Scheme.Modules.pullback (𝒰.f i)).map p)) : Epi p := by
  apply epi_of_pullback_opensCover (fun i => (𝒰.f i).opensRange)
    (IsOpenCover.mk 𝒰.iSup_opensRange)
  intro i
  let f := 𝒰.f i
  let g := f.isoOpensRange.inv
  let P := Scheme.Modules.pullback f
  let Q := Scheme.Modules.pullback g
  let e : P ⋙ Q ≅ Scheme.Modules.pullback f.opensRange.ι :=
    Scheme.Modules.pullbackComp g f ≪≫ Scheme.Modules.pullbackCongr f.isoOpensRange_inv_comp
  have : Epi (Q.map (P.map p)) := pullback_preserves_epi g _ (h i)
  have he : (Scheme.Modules.pullback f.opensRange.ι).map p =
      (e.app M).inv ≫ Q.map (P.map p) ≫ (e.app N).hom :=
    (e.app M).eq_inv_comp.mpr (e.hom.naturality p).symm
  rw [he]
  infer_instance

/-- Quotient presentations on the members of an open cover whose pullbacks agree glue to a
quotient presentation on the base, of which they are the pullbacks. -/
private lemma exists_glued_quotientPresentation {S : Scheme.{u}} {k n : ℕ}
    (𝒰 : S.OpenCover) (q : ∀ i, QuotientPresentation (𝒰.X i) k n)
    (h : ∀ (Y : Scheme.{u}) (a : Y ⟶ S) (i j : 𝒰.I₀)
      (g : Y ⟶ 𝒰.X i) (h : Y ⟶ 𝒰.X j),
      g ≫ 𝒰.f i = a → h ≫ 𝒰.f j = a →
      (pullbackPresentation g (q i)).Isomorphic
        (pullbackPresentation h (q j))) :
    ∃ Q : QuotientPresentation S k n,
      ∀ i, Q.IsPullback (𝒰.f i) (q i) := by
  obtain ⟨N, hN, p, e, he⟩ := exists_glued_quotientMap 𝒰 q h
  have hNr : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N (n - k) := by
    apply rank_of_openCover N (n - k) 𝒰
    intro i
    exact AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
      (e i).symm (q i).finiteLocallyFree
  exact ⟨⟨N, p, epi_of_pullback_openCover 𝒰 p
    (glued_quotientMap_pullback_epi 𝒰 q N p e he), hNr⟩,
    fun i => ⟨e i, he i⟩⟩

/-- `G(k, n)` satisfies the sheaf condition for the presieve of an open cover. -/
private lemma functor_isSheafFor_openCover (k n : ℕ) {S : Scheme.{u}}
    (𝒰 : S.OpenCover) :
    Presieve.IsSheafFor (functor.{u} k n) 𝒰.presieve₀ := by
  classical
  let F := functor.{u} k n
  let E := (functorData.{u} k n).objEquiv
  rw [PreZeroHypercover.presieve₀, Presieve.isSheafFor_arrows_iff]
  intro x hx
  choose q hq using fun i => Quotient.exists_rep (E (𝒰.X i) (x i))
  have hxi (i) : x i = (E (𝒰.X i)).symm ⟦q i⟧ := by
    apply (E (𝒰.X i)).injective
    simpa using (hq i).symm
  obtain ⟨Q, hQ⟩ := exists_glued_quotientPresentation 𝒰 q (by
    intro Y a i j g h hg hh
    apply quotientPresentation_isomorphic_of_eq
    have eq := congrArg (E Y) (hx i j Y g h (hg.trans hh.symm))
    rw [hxi i, hxi j] at eq
    rw [points_map_of_isPullback g (q i) _
      (pullbackPresentation_isPullback g (q i)),
      points_map_of_isPullback h (q j) _
      (pullbackPresentation_isPullback h (q j))] at eq
    exact eq)
  refine ⟨(E S).symm ⟦Q⟧, ?_, ?_⟩
  · intro i
    apply (E (𝒰.X i)).injective
    exact (points_map_of_isPullback (𝒰.f i) Q (q i) (hQ i)).trans (hq i)
  · intro y hy
    apply points_eq_of_openCover k n 𝒰
    intro i
    rw [hy i]
    apply (E (𝒰.X i)).injective
    exact (hq i).symm.trans
      (points_map_of_isPullback (𝒰.f i) Q (q i) (hQ i)).symm

/-- `G(k, n)` is a sheaf for the Zariski topology. -/
private lemma functor_isSheaf (k n : ℕ) :
    Presheaf.IsSheaf Scheme.zariskiTopology (functor.{u} k n) := by
  rw [isSheaf_iff_isSheaf_of_type]
  apply (Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange _).mpr
  intro S R hR
  obtain ⟨E, rfl⟩ := R.exists_eq_preZeroHypercover
  exact functor_isSheafFor_openCover k n ⟨E, hR⟩

end AlgebraicGeometry.Grassmannian

end
