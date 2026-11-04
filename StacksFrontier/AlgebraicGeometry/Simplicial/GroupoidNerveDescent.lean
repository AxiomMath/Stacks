module

public import StacksFrontier.AlgebraicGeometry.Simplicial.GroupoidNerve
public import StacksFrontier.AlgebraicGeometry.Groupoids.DescentIso
public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeLocality.GlobalSectionsAffineCase
public import StacksFrontier.AlgebraicGeometry.Simplicial.ZariskiQuasicoherentPair

/-!
# The cocycle condition of a pair in reindexed form

A pair `(ℱ, α)` on the total Zariski site of a simplicial scheme `X` (Stacks 07TH) carries the
cocycle condition in degree two, written with the compositors of the pullback of modules.  This
file rewrites it as an equation between reindexings of `α` along the three faces from degree two
to degree one, `AlgebraicGeometry.SimplicialScheme.ReindexCocycle`, and shows that this reindexed
form is the one of a groupoid descent morphism and that it is invariant under transport along
maps of the degrees and under reindexing along an isomorphism.  These are the steps that compare
pairs on the nerve of a groupoid scheme with groupoid descent data (Stacks 07TP).

## Main definitions

* `AlgebraicGeometry.SimplicialScheme.transportHom`: a morphism `t^*F ⟶ s^*G` transported along
  maps `e₀` and `e₁` relating `t, s` to `d₁, d₀`.
* `AlgebraicGeometry.SimplicialScheme.ReindexCocycle`: the cocycle condition in reindexed form.

## Main results

* `AlgebraicGeometry.SimplicialScheme.groupoid_cocycle_iff_reindexCocycle`: the cocycle
  condition of a groupoid descent morphism in reindexed form.
* `AlgebraicGeometry.SimplicialScheme.reindexCocycle_transportHom_iff`: invariance under
  transport.
* `AlgebraicGeometry.SimplicialScheme.reindexCocycle_comp_iff`: invariance under reindexing along
  an isomorphism.
* `AlgebraicGeometry.SimplicialScheme.isCocycle_iff_reindexCocycle`: the cocycle condition of a
  pair on a simplicial scheme is the reindexed cocycle condition.

## References

* [Stacks Project, Tag 07TH](https://stacks.math.columbia.edu/tag/07TH)
* [Stacks Project, Tag 07TP](https://stacks.math.columbia.edu/tag/07TP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
open Stacks.Groupoids

universe u

namespace AlgebraicGeometry.SimplicialScheme

section Coherence

variable {A B C D : Scheme.{u}}

/-- A pullback of a morphism between two pullbacks of a module, written with the reindexing of
that morphism. -/
theorem pullback_map_eq_reindexHom (f : A ⟶ B) {g h : B ⟶ C} {M : C.Modules}
    (β : (Scheme.Modules.pullback g).obj M ⟶ (Scheme.Modules.pullback h).obj M) :
    (Scheme.Modules.pullback f).map β =
      (Scheme.Modules.pullbackComp f g).hom.app M ≫ reindexHom f β ≫
        (Scheme.Modules.pullbackComp f h).inv.app M := by
  simp [reindexHom]

/-- **Coherence of the compositors at factorizations.** Pulling back the compositor of a
factorization `b ≫ c = b' ≫ c'` along `a` agrees, through the compositors, with the compositor
of the factorization `(a ≫ b) ≫ c = (a ≫ b') ≫ c'`. -/
theorem pullback_map_pullbackPasteOfEq (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D) {C' : Scheme.{u}}
    (b' : B ⟶ C') (c' : C' ⟶ D) (h : b ≫ c = b' ≫ c') (M : D.Modules) :
    (Scheme.Modules.pullback a).map (pullbackPasteOfEq b c (b' ≫ c') h M).hom =
      (Scheme.Modules.pullbackComp a b).hom.app ((Scheme.Modules.pullback c).obj M) ≫
        (pullbackPasteOfEq (a ≫ b) c ((a ≫ b') ≫ c')
          (by rw [Category.assoc, h, Category.assoc]) M).hom ≫
        (Scheme.Modules.pullbackComp (a ≫ b') c').inv.app M ≫
        (Scheme.Modules.pullbackComp a b').inv.app ((Scheme.Modules.pullback c').obj M) ≫
        (Scheme.Modules.pullback a).map ((Scheme.Modules.pullbackComp b' c').hom.app M) := by
  have h1 := pullbackPasteOfEq_assoc a b c (a ≫ b) rfl (b' ≫ c') h ((a ≫ b') ≫ c')
    (by rw [Category.assoc, h, Category.assoc]) (a ≫ b' ≫ c') rfl (by rw [Category.assoc]) M
  have h2 := pullbackPasteOfEq_assoc a b' c' (a ≫ b') rfl (b' ≫ c') rfl ((a ≫ b') ≫ c') rfl
    (a ≫ b' ≫ c') rfl (by rw [Category.assoc]) M
  simp only [pullbackPasteOfEq, Iso.trans_hom, Iso.app_hom, Scheme.Modules.pullbackCongr,
    eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.comp_id] at h2
  rw [← cancel_mono ((pullbackPasteOfEq a (b' ≫ c') (a ≫ b' ≫ c') rfl M).hom ≫
    eqToHom (congrArg (fun t => (Scheme.Modules.pullback t).obj M)
      (show a ≫ b' ≫ c' = (a ≫ b') ≫ c' by rw [Category.assoc])))]
  rw [← h1]
  simp only [pullbackPasteOfEq, Iso.trans_hom, Iso.app_hom, Scheme.Modules.pullbackCongr,
    eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.comp_id, Category.assoc]
  rw [← h2]
  simp

variable {T Y₁ Y₀ R U : Scheme.{u}}

/-- **The transport of a morphism between pullbacks along a map of the targets.** For maps
`d₁ d₀ : Y₁ ⟶ Y₀` and `t s : R ⟶ U` related by `e₀ : Y₀ ⟶ U` and `e₁ : Y₁ ⟶ R`, a morphism
`γ : t^* F ⟶ s^* G` gives `d₁^* e₀^* F ⟶ d₀^* e₀^* G`: pull `γ` back along `e₁` and read it
through the compositors. -/
noncomputable def transportHom {d₁ d₀ : Y₁ ⟶ Y₀} {e₀ : Y₀ ⟶ U} {e₁ : Y₁ ⟶ R} {t s : R ⟶ U}
    (h₁ : d₁ ≫ e₀ = e₁ ≫ t) (h₀ : d₀ ≫ e₀ = e₁ ≫ s) {F G : U.Modules}
    (γ : (Scheme.Modules.pullback t).obj F ⟶ (Scheme.Modules.pullback s).obj G) :
    (Scheme.Modules.pullback d₁).obj ((Scheme.Modules.pullback e₀).obj F) ⟶
      (Scheme.Modules.pullback d₀).obj ((Scheme.Modules.pullback e₀).obj G) :=
  (pullbackPasteOfEq d₁ e₀ (e₁ ≫ t) h₁ F).hom ≫ (Scheme.Modules.pullbackComp e₁ t).inv.app F ≫
    (Scheme.Modules.pullback e₁).map γ ≫ (Scheme.Modules.pullbackComp e₁ s).hom.app G ≫
      (pullbackPasteOfEq d₀ e₀ (e₁ ≫ s) h₀ G).inv

/-- `pullback_map_pullbackPasteOfEq` for the inverse of the compositor. -/
theorem pullback_map_pullbackPasteOfEq_inv (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D) {C' : Scheme.{u}}
    (b' : B ⟶ C') (c' : C' ⟶ D) (h : b ≫ c = b' ≫ c') (M : D.Modules) :
    (Scheme.Modules.pullback a).map (pullbackPasteOfEq b c (b' ≫ c') h M).inv =
      (Scheme.Modules.pullback a).map ((Scheme.Modules.pullbackComp b' c').inv.app M) ≫
        (Scheme.Modules.pullbackComp a b').hom.app ((Scheme.Modules.pullback c').obj M) ≫
        (Scheme.Modules.pullbackComp (a ≫ b') c').hom.app M ≫
        (pullbackPasteOfEq (a ≫ b) c ((a ≫ b') ≫ c')
          (by rw [Category.assoc, h, Category.assoc]) M).inv ≫
        (Scheme.Modules.pullbackComp a b).inv.app ((Scheme.Modules.pullback c).obj M) := by
  rw [← cancel_epi ((Scheme.Modules.pullback a).map (pullbackPasteOfEq b c (b' ≫ c') h M).hom),
    ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
    pullback_map_pullbackPasteOfEq]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_assoc,
    Functor.comp_obj]

/-- **Reindexing a transported morphism** along `p : T ⟶ Y₁` is reindexing the original morphism
along `p ≫ e₁`, read through the compositors. -/
theorem reindexHom_transportHom (p : T ⟶ Y₁) {d₁ d₀ : Y₁ ⟶ Y₀} {e₀ : Y₀ ⟶ U} {e₁ : Y₁ ⟶ R}
    {t s : R ⟶ U} (h₁ : d₁ ≫ e₀ = e₁ ≫ t) (h₀ : d₀ ≫ e₀ = e₁ ≫ s) {F : U.Modules}
    (γ : (Scheme.Modules.pullback t).obj F ⟶ (Scheme.Modules.pullback s).obj F) :
    reindexHom p (transportHom h₁ h₀ γ) =
      (pullbackPasteOfEq (p ≫ d₁) e₀ ((p ≫ e₁) ≫ t)
          (by rw [Category.assoc, h₁, Category.assoc]) F).hom ≫ reindexHom (p ≫ e₁) γ ≫
        (pullbackPasteOfEq (p ≫ d₀) e₀ ((p ≫ e₁) ≫ s)
          (by rw [Category.assoc, h₀, Category.assoc]) F).inv := by
  unfold reindexHom transportHom
  simp only [Functor.map_comp, pullback_map_pullbackPasteOfEq, pullback_map_pullbackPasteOfEq_inv,
    Category.assoc]
  have hn : (Scheme.Modules.pullbackComp p e₁).inv.app ((Scheme.Modules.pullback t).obj F) ≫
      (Scheme.Modules.pullback p).map ((Scheme.Modules.pullback e₁).map γ) ≫
        (Scheme.Modules.pullbackComp p e₁).hom.app ((Scheme.Modules.pullback s).obj F) =
      (Scheme.Modules.pullback (p ≫ e₁)).map γ := by
    have := (Scheme.Modules.pullbackComp p e₁).hom.naturality γ
    simp only [Functor.comp_map] at this
    rw [this, Iso.inv_hom_id_app_assoc]
  have c : ∀ r : R ⟶ U,
      (Scheme.Modules.pullback p).map ((Scheme.Modules.pullbackComp e₁ r).hom.app F) ≫
        (Scheme.Modules.pullback p).map ((Scheme.Modules.pullbackComp e₁ r).inv.app F) = 𝟙 _ := by
    intro r
    rw [← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
  rw [Iso.inv_hom_id_app_assoc, reassoc_of% (c t), reassoc_of% (c s), reassoc_of% hn,
    Iso.inv_hom_id_app, Category.comp_id]

/-- The compositor at a factorization is compatible with the comparison of pullbacks along two
equal morphisms. -/
theorem pullbackCongr_comp_pullbackPasteOfEq {x y : A ⟶ B} (hxy : x = y) (e : B ⟶ C)
    {kx ky : A ⟶ C} (hx : x ≫ e = kx) (hy : y ≫ e = ky) (hk : kx = ky) (M : C.Modules) :
    (Scheme.Modules.pullbackCongr hxy).hom.app ((Scheme.Modules.pullback e).obj M) ≫
        (pullbackPasteOfEq y e ky hy M).hom =
      (pullbackPasteOfEq x e kx hx M).hom ≫ (Scheme.Modules.pullbackCongr hk).hom.app M := by
  subst hxy hx hk
  simp [pullbackPasteOfEq, Scheme.Modules.pullbackCongr]

end Coherence

/-! ### The cocycle condition in reindexed form -/

section ReindexCocycle

variable {Y₂ Y₁ Y₀ : Scheme.{u}}

/-- **The cocycle condition in reindexed form.** For maps `p₀ p₁ p₂ : Y₂ ⟶ Y₁` and
`d₀ d₁ : Y₁ ⟶ Y₀` with `p₂ ≫ d₁ = p₁ ≫ d₁`, `p₂ ≫ d₀ = p₀ ≫ d₁` and `p₀ ≫ d₀ = p₁ ≫ d₀`, a
morphism `β : d₁^* M ⟶ d₀^* M` satisfies the cocycle condition when its reindexing along `p₁` is
the composite of its reindexings along `p₂` and `p₀`. -/
def ReindexCocycle {M : Y₀.Modules} (p₀ p₁ p₂ : Y₂ ⟶ Y₁) (d₀ d₁ : Y₁ ⟶ Y₀)
    (h₂₁ : p₂ ≫ d₁ = p₁ ≫ d₁) (h₂₀ : p₂ ≫ d₀ = p₀ ≫ d₁) (h₀₁ : p₀ ≫ d₀ = p₁ ≫ d₀)
    (β : (Scheme.Modules.pullback d₁).obj M ⟶ (Scheme.Modules.pullback d₀).obj M) : Prop :=
  reindexHom p₁ β =
    (Scheme.Modules.pullbackCongr h₂₁.symm).hom.app M ≫ reindexHom p₂ β ≫
      (Scheme.Modules.pullbackCongr h₂₀).hom.app M ≫ reindexHom p₀ β ≫
        (Scheme.Modules.pullbackCongr h₀₁).hom.app M

/-- The cocycle condition in reindexed form depends on the three maps only through their values. -/
theorem reindexCocycle_congr {M : Y₀.Modules} {p₀ p₁ p₂ p₀' p₁' p₂' : Y₂ ⟶ Y₁} {d₀ d₁ : Y₁ ⟶ Y₀}
    (e₀ : p₀ = p₀') (e₁ : p₁ = p₁') (e₂ : p₂ = p₂')
    (h₂₁ : p₂ ≫ d₁ = p₁ ≫ d₁) (h₂₀ : p₂ ≫ d₀ = p₀ ≫ d₁) (h₀₁ : p₀ ≫ d₀ = p₁ ≫ d₀)
    (h₂₁' : p₂' ≫ d₁ = p₁' ≫ d₁) (h₂₀' : p₂' ≫ d₀ = p₀' ≫ d₁) (h₀₁' : p₀' ≫ d₀ = p₁' ≫ d₀)
    (β : (Scheme.Modules.pullback d₁).obj M ⟶ (Scheme.Modules.pullback d₀).obj M) :
    ReindexCocycle p₀ p₁ p₂ d₀ d₁ h₂₁ h₂₀ h₀₁ β ↔
      ReindexCocycle p₀' p₁' p₂' d₀ d₁ h₂₁' h₂₀' h₀₁' β := by
  subst e₀ e₁ e₂
  exact Iff.rfl

end ReindexCocycle

section Groupoid

open Stacks.Groupoids.GroupoidScheme

variable {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S)

/-- **The cocycle condition of a groupoid descent morphism is the reindexed cocycle condition**
for the two projections and the composition law of the scheme of composable arrows. -/
theorem groupoid_cocycle_iff_reindexCocycle {F : G.objects.left.Modules}
    (α : (Scheme.Modules.pullback G.target.left).obj F ⟶
      (Scheme.Modules.pullback G.source.left).obj F) :
    successiveDescent G α = reindexHom G.comp.left α ↔
      ReindexCocycle (pullback.snd G.source G.target).left G.comp.left
        (pullback.fst G.source G.target).left G.source.left G.target.left
        (congrArg Over.Hom.left G.target_comp).symm
        (congrArg Over.Hom.left (pullback.condition : pullback.fst G.source G.target ≫ G.source =
          pullback.snd G.source G.target ≫ G.target))
        (congrArg Over.Hom.left G.source_comp).symm α :=
  ⟨fun h => h.symm, fun h => h.symm⟩

end Groupoid

section Transport

variable {Y₂ Y₁ Y₀ R U : Scheme.{u}}

/-- **The reindexed cocycle condition is invariant under transport.** A morphism transported
along `e₀ : Y₀ ⟶ U` and `e₁ : Y₁ ⟶ R` satisfies the reindexed cocycle condition for
`p₀ p₁ p₂ : Y₂ ⟶ Y₁` exactly when the original morphism satisfies it for the composites with
`e₁`. -/
theorem reindexCocycle_transportHom_iff (p₀ p₁ p₂ : Y₂ ⟶ Y₁) {d₀ d₁ : Y₁ ⟶ Y₀} {e₀ : Y₀ ⟶ U}
    {e₁ : Y₁ ⟶ R} {t s : R ⟶ U} (h₁ : d₁ ≫ e₀ = e₁ ≫ t) (h₀ : d₀ ≫ e₀ = e₁ ≫ s)
    {F : U.Modules}
    (γ : (Scheme.Modules.pullback t).obj F ⟶ (Scheme.Modules.pullback s).obj F)
    (h₂₁ : p₂ ≫ d₁ = p₁ ≫ d₁) (h₂₀ : p₂ ≫ d₀ = p₀ ≫ d₁) (h₀₁ : p₀ ≫ d₀ = p₁ ≫ d₀)
    (h₂₁' : (p₂ ≫ e₁) ≫ t = (p₁ ≫ e₁) ≫ t) (h₂₀' : (p₂ ≫ e₁) ≫ s = (p₀ ≫ e₁) ≫ t)
    (h₀₁' : (p₀ ≫ e₁) ≫ s = (p₁ ≫ e₁) ≫ s) :
    ReindexCocycle p₀ p₁ p₂ d₀ d₁ h₂₁ h₂₀ h₀₁ (transportHom h₁ h₀ γ) ↔
      ReindexCocycle (p₀ ≫ e₁) (p₁ ≫ e₁) (p₂ ≫ e₁) s t h₂₁' h₂₀' h₀₁' γ := by
  unfold ReindexCocycle
  rw [reindexHom_transportHom, reindexHom_transportHom, reindexHom_transportHom]
  have a₂₁ := pullbackCongr_comp_pullbackPasteOfEq h₂₁.symm e₀
    (by rw [Category.assoc, h₁, Category.assoc] : (p₁ ≫ d₁) ≫ e₀ = (p₁ ≫ e₁) ≫ t)
    (by rw [Category.assoc, h₁, Category.assoc] : (p₂ ≫ d₁) ≫ e₀ = (p₂ ≫ e₁) ≫ t) h₂₁'.symm F
  have a₂₀ := pullbackCongr_comp_pullbackPasteOfEq h₂₀ e₀
    (by rw [Category.assoc, h₀, Category.assoc] : (p₂ ≫ d₀) ≫ e₀ = (p₂ ≫ e₁) ≫ s)
    (by rw [Category.assoc, h₁, Category.assoc] : (p₀ ≫ d₁) ≫ e₀ = (p₀ ≫ e₁) ≫ t) h₂₀' F
  have a₀₁ := pullbackCongr_comp_pullbackPasteOfEq h₀₁ e₀
    (by rw [Category.assoc, h₀, Category.assoc] : (p₀ ≫ d₀) ≫ e₀ = (p₀ ≫ e₁) ≫ s)
    (by rw [Category.assoc, h₀, Category.assoc] : (p₁ ≫ d₀) ≫ e₀ = (p₁ ≫ e₁) ≫ s) h₀₁' F
  have a₀₁' : (pullbackPasteOfEq (p₀ ≫ d₀) e₀ ((p₀ ≫ e₁) ≫ s)
        (by rw [Category.assoc, h₀, Category.assoc]) F).inv ≫
      (Scheme.Modules.pullbackCongr h₀₁).hom.app ((Scheme.Modules.pullback e₀).obj F) =
      (Scheme.Modules.pullbackCongr h₀₁').hom.app F ≫ (pullbackPasteOfEq (p₁ ≫ d₀) e₀
        ((p₁ ≫ e₁) ≫ s) (by rw [Category.assoc, h₀, Category.assoc]) F).inv := by
    rw [Iso.inv_comp_eq, ← reassoc_of% a₀₁, Iso.hom_inv_id, Category.comp_id]
  have a₂₀' : (pullbackPasteOfEq (p₂ ≫ d₀) e₀ ((p₂ ≫ e₁) ≫ s)
        (by rw [Category.assoc, h₀, Category.assoc]) F).inv ≫
      (Scheme.Modules.pullbackCongr h₂₀).hom.app ((Scheme.Modules.pullback e₀).obj F) ≫
        (pullbackPasteOfEq (p₀ ≫ d₁) e₀ ((p₀ ≫ e₁) ≫ t)
          (by rw [Category.assoc, h₁, Category.assoc]) F).hom =
      (Scheme.Modules.pullbackCongr h₂₀').hom.app F := by
    rw [a₂₀, Iso.inv_hom_id_assoc]
  simp only [Category.assoc]
  rw [reassoc_of% a₂₁, reassoc_of% a₂₀', a₀₁', Iso.cancel_iso_hom_left]
  simp only [← Category.assoc]
  rw [Iso.cancel_iso_inv_right]

end Transport

/-! ### The cocycle condition of a pair of a simplicial scheme in reindexed form -/

section Simplicial

variable (X : SimplicialObject Scheme.{u})

/-- The identification of two factorizations in the family of modules on the degrees of a
simplicial scheme, through the compositors. -/
theorem zariskiModuleFamily_glueOfEq_hom {l m n : SimplexCategory} (ψ ψ' : l ⟶ m) (φ φ' : m ⟶ n)
    (v : l ⟶ n) (h : ψ ≫ φ = v) (h' : ψ' ≫ φ' = v) (F : (X.obj (op l)).Modules) :
    ((zariskiModuleFamily X).glueOfEq ψ ψ' φ φ' v h h' F).hom =
      (Scheme.Modules.pullbackComp (X.map φ.op) (X.map ψ.op)).hom.app F ≫
        (Scheme.Modules.pullbackCongr (show X.map φ.op ≫ X.map ψ.op = X.map φ'.op ≫ X.map ψ'.op by
          rw [← X.map_comp, ← X.map_comp, ← op_comp, ← op_comp, h, h'])).hom.app F ≫
        (Scheme.Modules.pullbackComp (X.map φ'.op) (X.map ψ'.op)).inv.app F := by
  subst h
  simp only [SimplicialPseudoFamily.glueOfEq, SimplicialPseudoFamily.pasteOfEq, Iso.trans_hom,
    Iso.symm_hom, Iso.trans_inv, pullbackPasteOfEq, Iso.app_hom, Iso.app_inv,
    Scheme.Modules.pullbackCongr, eqToIso.hom, eqToIso.inv, eqToHom_app, Category.assoc,
    eqToHom_trans_assoc]

/-- The relation between the face maps of a simplicial scheme from degree two to degree zero along
`δ¹₁`, through `δ²₂` and `δ²₁`. -/
theorem map_delta_two_one {X : SimplicialObject Scheme.{u}} :
    X.map (@SimplexCategory.δ (0 + 1) (2 : Fin 3)).op ≫ X.map (SimplexCategory.δ (1 : Fin 2)).op =
      X.map (@SimplexCategory.δ (0 + 1) (1 : Fin 3)).op ≫
        X.map (SimplexCategory.δ (1 : Fin 2)).op := by
  rw [← X.map_comp, ← X.map_comp, ← op_comp, ← op_comp, SimplexCategory.delta_one_comp_delta_two,
    SimplexCategory.delta_one_comp_delta_one]

/-- The relation between the face maps of a simplicial scheme from degree two to degree zero
through `δ²₂ ≫ δ¹₀` and `δ²₀ ≫ δ¹₁`. -/
theorem map_delta_two_zero {X : SimplicialObject Scheme.{u}} :
    X.map (@SimplexCategory.δ (0 + 1) (2 : Fin 3)).op ≫ X.map (SimplexCategory.δ (0 : Fin 2)).op =
      X.map (@SimplexCategory.δ (0 + 1) (0 : Fin 3)).op ≫
        X.map (SimplexCategory.δ (1 : Fin 2)).op := by
  rw [← X.map_comp, ← X.map_comp, ← op_comp, ← op_comp, SimplexCategory.delta_zero_comp_delta_two,
    SimplexCategory.delta_one_comp_delta_zero]

/-- The relation between the face maps of a simplicial scheme from degree two to degree zero along
`δ¹₀`, through `δ²₀` and `δ²₁`. -/
theorem map_delta_zero_one {X : SimplicialObject Scheme.{u}} :
    X.map (@SimplexCategory.δ (0 + 1) (0 : Fin 3)).op ≫ X.map (SimplexCategory.δ (0 : Fin 2)).op =
      X.map (@SimplexCategory.δ (0 + 1) (1 : Fin 3)).op ≫
        X.map (SimplexCategory.δ (0 : Fin 2)).op := by
  rw [← X.map_comp, ← X.map_comp, ← op_comp, ← op_comp, SimplexCategory.delta_zero_comp_delta_zero,
    SimplexCategory.delta_zero_comp_delta_one]

/-- An equation of composites conjugated by isomorphisms and transports, reduced to the
unconjugated equation. -/
theorem comp_eq_iff_of_conj {Y : Scheme.{u}} {A A' B B' P₁ P₂ Q₁ Q₂ S₁ S₂ T₁ T₂ : Y.Modules}
    (c₁ : A ⟶ A') (R₁ : A' ⟶ B') (c₁' : B' ⟶ B) (E₁ : A ⟶ P₁) (c₂ : P₁ ⟶ P₂) (R₂ : P₂ ⟶ Q₂)
    (c₂' : Q₂ ⟶ Q₁) (E₂ : Q₁ ⟶ S₁) (c₀ : S₁ ⟶ S₂) (R₀ : S₂ ⟶ T₂) (c₀' : T₂ ⟶ T₁)
    (E₃ : T₁ ⟶ B) (k₁ : A' ⟶ P₂) (k₂ : Q₂ ⟶ S₂) (k₃ : T₂ ⟶ B') [IsIso c₁] [IsIso c₁']
    (h₁ : E₁ ≫ c₂ = c₁ ≫ k₁) (h₂ : c₂' ≫ E₂ ≫ c₀ = k₂) (h₃ : c₀' ≫ E₃ = k₃ ≫ c₁') :
    c₁ ≫ R₁ ≫ c₁' = E₁ ≫ c₂ ≫ R₂ ≫ c₂' ≫ E₂ ≫ c₀ ≫ R₀ ≫ c₀' ≫ E₃ ↔
      R₁ = k₁ ≫ R₂ ≫ k₂ ≫ R₀ ≫ k₃ := by
  rw [reassoc_of% h₁, ← h₂, h₃]
  simp only [Category.assoc, cancel_epi]
  simp only [← Category.assoc, cancel_mono]

/-- Two composites of two comparisons of pullbacks with the same ends agree. -/
theorem pullbackCongr_comp_eq_comp {A B : Scheme.{u}} {f g h k : A ⟶ B} (p : f = g) (q : g = h)
    (r : f = k) (s : k = h) (M : B.Modules) :
    (Scheme.Modules.pullbackCongr p).hom.app M ≫ (Scheme.Modules.pullbackCongr q).hom.app M =
      (Scheme.Modules.pullbackCongr r).hom.app M ≫ (Scheme.Modules.pullbackCongr s).hom.app M := by
  subst p q s
  rfl

/-- A composite of three comparisons of pullbacks is the comparison of the ends. -/
theorem pullbackCongr_comp_comp {A B : Scheme.{u}} {f g h k : A ⟶ B} (p : f = g) (q : g = h)
    (r : h = k) (s : f = k) (M : B.Modules) :
    (Scheme.Modules.pullbackCongr p).hom.app M ≫ (Scheme.Modules.pullbackCongr q).hom.app M ≫
      (Scheme.Modules.pullbackCongr r).hom.app M = (Scheme.Modules.pullbackCongr s).hom.app M := by
  subst p q r
  simp [Scheme.Modules.pullbackCongr]

/-- The reindexing of the family of modules on the degrees of a simplicial scheme is the
reindexing of morphisms of modules on schemes, read through the comparisons of pullbacks along
`X.map_comp`. -/
theorem zariskiModuleFamily_reindexP {l m n : SimplexCategory} (ψ ψ' : l ⟶ m) (φ : m ⟶ n)
    {M : (X.obj (op l)).Modules}
    (β : (Scheme.Modules.pullback (X.map ψ.op)).obj M ⟶
      (Scheme.Modules.pullback (X.map ψ'.op)).obj M) :
    SimplicialPseudoFamily.reindexP (P := zariskiModuleFamily X) ψ ψ' φ β =
      (Scheme.Modules.pullbackCongr (map_op_comp_map_op X ψ φ).symm).hom.app M ≫
        reindexHom (X.map φ.op) β ≫
        (Scheme.Modules.pullbackCongr (map_op_comp_map_op X ψ' φ)).hom.app M := by
  simp [SimplicialPseudoFamily.reindexP, reindexHom, pullbackPasteOfEq,
    Scheme.Modules.pullbackCongr]

/-- The transport along an equality of simplex maps in the family of modules on the degrees of a
simplicial scheme is the comparison of pullbacks along the equal morphisms of schemes. -/
theorem zariskiModuleFamily_eqToHom {l m : SimplexCategory} {k k' : l ⟶ m} (h : k = k')
    (F : (X.obj (op l)).Modules)
    (p : ((zariskiModuleFamily X).map k).obj F = ((zariskiModuleFamily X).map k').obj F) :
    eqToHom p =
      (Scheme.Modules.pullbackCongr (show X.map k.op = X.map k'.op by rw [h])).hom.app F := by
  subst h
  simp [Scheme.Modules.pullbackCongr]

section CocycleAt

variable {o₀ o₁ o₂ : SimplexCategory} (a₀ a₁ : o₀ ⟶ o₁) (b₀ b₁ b₂ : o₁ ⟶ o₂)
    (e₂₁ : a₁ ≫ b₁ = a₁ ≫ b₂) (e₂₀ : a₀ ≫ b₂ = a₁ ≫ b₀) (e₀₁ : a₀ ≫ b₀ = a₀ ≫ b₁)
    (F : (X.obj (op o₀)).Modules)
    (α : (Scheme.Modules.pullback (X.map a₁.op)).obj F ⟶
      (Scheme.Modules.pullback (X.map a₀.op)).obj F)

/-- The last two steps of the reindexed cocycle condition of the family of modules on the degrees
of a simplicial scheme, read as morphisms of modules. -/
theorem zariskiModuleFamily_reindexP_comp_eqToHom :
    SimplicialPseudoFamily.reindexP (P := zariskiModuleFamily X) a₁ a₀ b₀ α ≫
      eqToHom (show ((zariskiModuleFamily X).map (a₀ ≫ b₀)).obj F =
        ((zariskiModuleFamily X).map (a₀ ≫ b₁)).obj F by rw [e₀₁]) =
    ((Scheme.Modules.pullbackCongr (map_op_comp_map_op X a₁ b₀).symm).hom.app F ≫
        reindexHom (X.map b₀.op) α ≫
        (Scheme.Modules.pullbackCongr (map_op_comp_map_op X a₀ b₀)).hom.app F) ≫
      (Scheme.Modules.pullbackCongr (show X.map (a₀ ≫ b₀).op = X.map (a₀ ≫ b₁).op by
          rw [e₀₁])).hom.app F := by
  rewrite [zariskiModuleFamily_reindexP, zariskiModuleFamily_eqToHom]
  · rfl
  · exact e₀₁

/-- The first three steps of the reindexed cocycle condition of the family of modules on the
degrees of a simplicial scheme, followed by any morphism, read as morphisms of modules. -/
theorem eqToHom_comp_zariskiModuleFamily_reindexP_comp
    (Z : ((zariskiModuleFamily X).map (a₁ ≫ b₀)).obj F ⟶
      ((zariskiModuleFamily X).map (a₀ ≫ b₁)).obj F) :
    eqToHom (show ((zariskiModuleFamily X).map (a₁ ≫ b₁)).obj F =
        ((zariskiModuleFamily X).map (a₁ ≫ b₂)).obj F by rw [e₂₁]) ≫
      SimplicialPseudoFamily.reindexP (P := zariskiModuleFamily X) a₁ a₀ b₂ α ≫
      eqToHom (show ((zariskiModuleFamily X).map (a₀ ≫ b₂)).obj F =
        ((zariskiModuleFamily X).map (a₁ ≫ b₀)).obj F by rw [e₂₀]) ≫ Z =
    (Scheme.Modules.pullbackCongr (show X.map (a₁ ≫ b₁).op = X.map (a₁ ≫ b₂).op by
          rw [e₂₁])).hom.app F ≫
      ((Scheme.Modules.pullbackCongr (map_op_comp_map_op X a₁ b₂).symm).hom.app F ≫
        reindexHom (X.map b₂.op) α ≫
        (Scheme.Modules.pullbackCongr (map_op_comp_map_op X a₀ b₂)).hom.app F) ≫
      (Scheme.Modules.pullbackCongr (show X.map (a₀ ≫ b₂).op = X.map (a₁ ≫ b₀).op by
          rw [e₂₀])).hom.app F ≫ Z := by
  rewrite [zariskiModuleFamily_reindexP, zariskiModuleFamily_eqToHom,
    zariskiModuleFamily_eqToHom]
  · rfl
  all_goals first | exact e₂₁ | exact e₂₀

/-- The reindexed cocycle condition of the family of modules on the degrees of a simplicial scheme,
with its right-hand side read as a composite of morphisms of modules. -/
theorem isReindexCocycleAt_iff_eq :
    (zariskiModuleFamily X).IsReindexCocycleAt a₀ a₁ b₀ b₁ b₂ e₂₁ e₂₀ e₀₁ F α ↔
    SimplicialPseudoFamily.reindexP (P := zariskiModuleFamily X) a₁ a₀ b₁ α =
    (Scheme.Modules.pullbackCongr (show X.map (a₁ ≫ b₁).op = X.map (a₁ ≫ b₂).op by
          rw [e₂₁])).hom.app F ≫
      ((Scheme.Modules.pullbackCongr (map_op_comp_map_op X a₁ b₂).symm).hom.app F ≫
        reindexHom (X.map b₂.op) α ≫
        (Scheme.Modules.pullbackCongr (map_op_comp_map_op X a₀ b₂)).hom.app F) ≫
      (Scheme.Modules.pullbackCongr (show X.map (a₀ ≫ b₂).op = X.map (a₁ ≫ b₀).op by
          rw [e₂₀])).hom.app F ≫
      ((Scheme.Modules.pullbackCongr (map_op_comp_map_op X a₁ b₀).symm).hom.app F ≫
        reindexHom (X.map b₀.op) α ≫
        (Scheme.Modules.pullbackCongr (map_op_comp_map_op X a₀ b₀)).hom.app F) ≫
      (Scheme.Modules.pullbackCongr (show X.map (a₀ ≫ b₀).op = X.map (a₀ ≫ b₁).op by
          rw [e₀₁])).hom.app F := by
  unfold SimplicialPseudoFamily.IsReindexCocycleAt
  rw [zariskiModuleFamily_reindexP_comp_eqToHom X a₀ a₁ b₀ b₁ e₀₁ F α,
    eqToHom_comp_zariskiModuleFamily_reindexP_comp X a₀ a₁ b₀ b₁ b₂ e₂₁ e₂₀ F α]

/-- **The reindexed cocycle condition of the family of modules on the degrees of a simplicial
scheme is the reindexed cocycle condition of modules**, at arbitrary faces. -/
theorem isReindexCocycleAt_iff
    (h₂₁ : X.map b₂.op ≫ X.map a₁.op = X.map b₁.op ≫ X.map a₁.op)
    (h₂₀ : X.map b₂.op ≫ X.map a₀.op = X.map b₀.op ≫ X.map a₁.op)
    (h₀₁ : X.map b₀.op ≫ X.map a₀.op = X.map b₁.op ≫ X.map a₀.op) :
    (zariskiModuleFamily X).IsReindexCocycleAt a₀ a₁ b₀ b₁ b₂ e₂₁ e₂₀ e₀₁ F α ↔
      ReindexCocycle (X.map b₀.op) (X.map b₁.op) (X.map b₂.op) (X.map a₀.op) (X.map a₁.op)
        h₂₁ h₂₀ h₀₁ α := by
  rw [isReindexCocycleAt_iff_eq X a₀ a₁ b₀ b₁ b₂ e₂₁ e₂₀ e₀₁ F α, zariskiModuleFamily_reindexP]
  unfold ReindexCocycle
  simp only [Category.assoc]
  refine comp_eq_iff_of_conj (Y := X.obj (op o₂))
    (A := (Scheme.Modules.pullback (X.map (a₁ ≫ b₁).op)).obj F)
    (A' := (Scheme.Modules.pullback (X.map b₁.op ≫ X.map a₁.op)).obj F)
    (B := (Scheme.Modules.pullback (X.map (a₀ ≫ b₁).op)).obj F)
    (B' := (Scheme.Modules.pullback (X.map b₁.op ≫ X.map a₀.op)).obj F)
    (P₁ := (Scheme.Modules.pullback (X.map (a₁ ≫ b₂).op)).obj F)
    (P₂ := (Scheme.Modules.pullback (X.map b₂.op ≫ X.map a₁.op)).obj F)
    (Q₁ := (Scheme.Modules.pullback (X.map (a₀ ≫ b₂).op)).obj F)
    (Q₂ := (Scheme.Modules.pullback (X.map b₂.op ≫ X.map a₀.op)).obj F)
    (S₁ := (Scheme.Modules.pullback (X.map (a₁ ≫ b₀).op)).obj F)
    (S₂ := (Scheme.Modules.pullback (X.map b₀.op ≫ X.map a₁.op)).obj F)
    (T₁ := (Scheme.Modules.pullback (X.map (a₀ ≫ b₀).op)).obj F)
    (T₂ := (Scheme.Modules.pullback (X.map b₀.op ≫ X.map a₀.op)).obj F)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
  · exact pullbackCongr_comp_eq_comp _ _ _ _ F
  · exact pullbackCongr_comp_comp _ _ _ _ F
  · exact pullbackCongr_comp_eq_comp _ _ _ _ F

end CocycleAt

/-- **The cocycle condition of a pair on a simplicial scheme is the reindexed cocycle condition**
for the three faces from degree two to degree one. -/
theorem isCocycle_iff_reindexCocycle (F : (zariskiModuleFamily X).obj ⦋0⦌)
    (α : ((zariskiModuleFamily X).map (SimplexCategory.δ (1 : Fin 2))).obj F ≅
      ((zariskiModuleFamily X).map (SimplexCategory.δ (0 : Fin 2))).obj F) :
    (zariskiModuleFamily X).IsCocycle F α ↔
      ReindexCocycle (X.map (@SimplexCategory.δ (0 + 1) (0 : Fin 3)).op)
        (X.map (@SimplexCategory.δ (0 + 1) (1 : Fin 3)).op)
        (X.map (@SimplexCategory.δ (0 + 1) (2 : Fin 3)).op)
        (X.map (SimplexCategory.δ (0 : Fin 2)).op) (X.map (SimplexCategory.δ (1 : Fin 2)).op)
        map_delta_two_one map_delta_two_zero map_delta_zero_one α.hom :=
  ((zariskiModuleFamily X).isCocycle_iff_isReindexCocycle F α).trans
    (isReindexCocycleAt_iff X _ _ _ _ _ _ _ _ F α.hom _ _ _)

end Simplicial

/-! ### Naturality and bijectivity of the transport -/

section TransportNaturality

variable {Y₁ Y₀ R U : Scheme.{u}} {d₁ d₀ : Y₁ ⟶ Y₀} {e₀ : Y₀ ⟶ U} {e₁ : Y₁ ⟶ R} {t s : R ⟶ U}
  (h₁ : d₁ ≫ e₀ = e₁ ≫ t) (h₀ : d₀ ≫ e₀ = e₁ ≫ s)

/-- The transport is natural in the target module. -/
theorem transportHom_comp_map {F G G' : U.Modules}
    (γ : (Scheme.Modules.pullback t).obj F ⟶ (Scheme.Modules.pullback s).obj G) (f : G ⟶ G') :
    transportHom h₁ h₀ (γ ≫ (Scheme.Modules.pullback s).map f) =
      transportHom h₁ h₀ γ ≫
        (Scheme.Modules.pullback d₀).map ((Scheme.Modules.pullback e₀).map f) := by
  unfold transportHom
  simp only [Functor.map_comp, Category.assoc]
  have hn := (Scheme.Modules.pullbackComp e₁ s).hom.naturality f
  simp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
  congr 4
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
  exact (pullbackPasteOfEq_naturality d₀ e₀ (e₁ ≫ s) h₀ f).symm

/-- The transport is natural in the source module. -/
theorem map_comp_transportHom {F F' G : U.Modules} (f : F ⟶ F')
    (γ : (Scheme.Modules.pullback t).obj F' ⟶ (Scheme.Modules.pullback s).obj G) :
    transportHom h₁ h₀ ((Scheme.Modules.pullback t).map f ≫ γ) =
      (Scheme.Modules.pullback d₁).map ((Scheme.Modules.pullback e₀).map f) ≫
        transportHom h₁ h₀ γ := by
  unfold transportHom
  simp only [Functor.map_comp]
  rw [reassoc_of% (pullbackPasteOfEq_naturality d₁ e₀ (e₁ ≫ t) h₁ f)]
  congr 1
  have hn := (Scheme.Modules.pullbackComp e₁ t).inv.naturality f
  simp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
  simp only [Category.assoc]

/-- The transport of an isomorphism is an isomorphism. -/
instance isIso_transportHom {F G : U.Modules}
    (γ : (Scheme.Modules.pullback t).obj F ⟶ (Scheme.Modules.pullback s).obj G) [IsIso γ] :
    IsIso (transportHom h₁ h₀ γ) := by
  unfold transportHom
  infer_instance

/-- Pulling back a morphism along `e₁` is its transport, read through the compositors. -/
private theorem pullback_map_eq_transportHom {F G : U.Modules}
    (γ : (Scheme.Modules.pullback t).obj F ⟶ (Scheme.Modules.pullback s).obj G) :
    (Scheme.Modules.pullback e₁).map γ =
      (Scheme.Modules.pullbackComp e₁ t).hom.app F ≫
        (pullbackPasteOfEq d₁ e₀ (e₁ ≫ t) h₁ F).inv ≫ transportHom h₁ h₀ γ ≫
          (pullbackPasteOfEq d₀ e₀ (e₁ ≫ s) h₀ G).hom ≫
            (Scheme.Modules.pullbackComp e₁ s).inv.app G := by
  unfold transportHom
  simp

variable [IsIso e₁]

/-- The transport along an isomorphism `e₁` is injective. -/
theorem transportHom_injective {F G : U.Modules} :
    Function.Injective (transportHom (F := F) (G := G) h₁ h₀) := by
  intro γ γ' h
  apply (Scheme.Modules.pullback e₁).map_injective
  rw [pullback_map_eq_transportHom h₁ h₀ γ, pullback_map_eq_transportHom h₁ h₀ γ', h]

/-- Every morphism `d₁^* e₀^* F ⟶ d₀^* e₀^* G` is a transport, when `e₁` is an isomorphism. -/
noncomputable def transportPreimage {F G : U.Modules}
    (β : (Scheme.Modules.pullback d₁).obj ((Scheme.Modules.pullback e₀).obj F) ⟶
      (Scheme.Modules.pullback d₀).obj ((Scheme.Modules.pullback e₀).obj G)) :
    (Scheme.Modules.pullback t).obj F ⟶ (Scheme.Modules.pullback s).obj G :=
  (Scheme.Modules.pullback e₁).preimage
    ((Scheme.Modules.pullbackComp e₁ t).hom.app F ≫ (pullbackPasteOfEq d₁ e₀ (e₁ ≫ t) h₁ F).inv ≫
      β ≫ (pullbackPasteOfEq d₀ e₀ (e₁ ≫ s) h₀ G).hom ≫
        (Scheme.Modules.pullbackComp e₁ s).inv.app G)

/-- The transport of `transportPreimage β` is `β`. -/
theorem transportHom_transportPreimage {F G : U.Modules}
    (β : (Scheme.Modules.pullback d₁).obj ((Scheme.Modules.pullback e₀).obj F) ⟶
      (Scheme.Modules.pullback d₀).obj ((Scheme.Modules.pullback e₀).obj G)) :
    transportHom h₁ h₀ (transportPreimage h₁ h₀ β) = β := by
  unfold transportHom transportPreimage
  simp

/-- A morphism whose transport along an isomorphism `e₁` is an isomorphism is an isomorphism. -/
theorem isIso_of_isIso_transportHom {F G : U.Modules}
    (γ : (Scheme.Modules.pullback t).obj F ⟶ (Scheme.Modules.pullback s).obj G)
    [IsIso (transportHom h₁ h₀ γ)] : IsIso γ := by
  have : IsIso ((Scheme.Modules.pullback e₁).map γ) := by
    rw [pullback_map_eq_transportHom h₁ h₀ γ]
    infer_instance
  exact isIso_of_fully_faithful (Scheme.Modules.pullback e₁) γ

end TransportNaturality

/-! ### The reindexed cocycle condition along an isomorphism -/

section AlongIso

variable {Y₂' Y₂ Y₁ Y₀ : Scheme.{u}}

/-- **The reindexed cocycle condition can be checked after reindexing along an isomorphism.** -/
theorem reindexCocycle_comp_iff (e : Y₂' ⟶ Y₂) [IsIso e] {M : Y₀.Modules}
    (p₀ p₁ p₂ : Y₂ ⟶ Y₁) (d₀ d₁ : Y₁ ⟶ Y₀)
    (h₂₁ : p₂ ≫ d₁ = p₁ ≫ d₁) (h₂₀ : p₂ ≫ d₀ = p₀ ≫ d₁) (h₀₁ : p₀ ≫ d₀ = p₁ ≫ d₀)
    (h₂₁' : (e ≫ p₂) ≫ d₁ = (e ≫ p₁) ≫ d₁) (h₂₀' : (e ≫ p₂) ≫ d₀ = (e ≫ p₀) ≫ d₁)
    (h₀₁' : (e ≫ p₀) ≫ d₀ = (e ≫ p₁) ≫ d₀)
    (β : (Scheme.Modules.pullback d₁).obj M ⟶ (Scheme.Modules.pullback d₀).obj M) :
    ReindexCocycle (e ≫ p₀) (e ≫ p₁) (e ≫ p₂) d₀ d₁ h₂₁' h₂₀' h₀₁' β ↔
      ReindexCocycle p₀ p₁ p₂ d₀ d₁ h₂₁ h₂₀ h₀₁ β := by
  have key : ∀ (x y : (Scheme.Modules.pullback (p₁ ≫ d₁)).obj M ⟶
      (Scheme.Modules.pullback (p₁ ≫ d₀)).obj M),
      reindexHom e x = reindexHom e y ↔ x = y := by
    intro x y
    refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
    unfold reindexHom at h
    simp only [cancel_epi, cancel_mono] at h
    exact (Scheme.Modules.pullback e).map_injective h
  have hR : (Scheme.Modules.pullbackCongr h₂₁'.symm).hom.app M ≫ reindexHom (e ≫ p₂) β ≫
      (Scheme.Modules.pullbackCongr h₂₀').hom.app M ≫ reindexHom (e ≫ p₀) β ≫
        (Scheme.Modules.pullbackCongr h₀₁').hom.app M =
      (Scheme.Modules.pullbackCongr (Category.assoc e p₁ d₁)).hom.app M ≫
        reindexHom e ((Scheme.Modules.pullbackCongr h₂₁.symm).hom.app M ≫ reindexHom p₂ β ≫
          (Scheme.Modules.pullbackCongr h₂₀).hom.app M ≫ reindexHom p₀ β ≫
            (Scheme.Modules.pullbackCongr h₀₁).hom.app M) ≫
        (Scheme.Modules.pullbackCongr (Category.assoc e p₁ d₀).symm).hom.app M := by
    rw [reindexHom_assoc, reindexHom_assoc, reindexHom_comp, reindexHom_comp, reindexHom_comp,
      reindexHom_comp, reindexHom_congr, reindexHom_congr, reindexHom_congr]
    simp only [Category.assoc, Stacks.Groupoids.pullbackCongr_hom_app_comp,
      Stacks.Groupoids.pullbackCongr_hom_app_comp_assoc]
  unfold ReindexCocycle
  rw [hR, reindexHom_assoc, cancel_epi]
  constructor
  · intro h
    exact (key _ _).1 ((cancel_mono _).1 h)
  · intro h
    rw [(key _ _).2 h]

end AlongIso

end AlgebraicGeometry.SimplicialScheme

end
