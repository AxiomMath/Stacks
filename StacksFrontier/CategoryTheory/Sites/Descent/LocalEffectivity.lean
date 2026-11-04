module

public import Mathlib.CategoryTheory.Sites.Descent.IsStack
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.SigmaSummands
public import StacksFrontier.AlgebraicGeometry.Descent.ZariskiModuleChartComparison

/-!
# Local effectivity of descent data

Let `F` be a pseudofunctor from the locally discrete bicategory on `Cᵒᵖ` to `Cat`, a prestack for a
topology `J`, and let `D` be a descent datum relative to a covering family `f i : X i ⟶ U`.  This
file develops the notion of an object `y` over `V` being identified with `D` along a morphism
`a : V ⟶ U`, `CategoryTheory.Pseudofunctor.DescentData.Identification`: a family of morphisms
`t^* y ⟶ h^* (D.obj i)` for `h ≫ f i = t ≫ a`, compatible with pullback and with the gluing
morphisms of `D`.  An identification along `𝟙 U` is the same as an isomorphism of `D` with the
descent datum of `y`, so the effectivity of `D` is the existence of such an identification, and
these identifications can be glued.

## Main results

* `CategoryTheory.Pseudofunctor.existsUnique_map_eq_of_isPrestack` and
  `CategoryTheory.Pseudofunctor.existsUnique_pullHom_eq_of_isPrestack`: morphisms glue over a
  covering sieve; `CategoryTheory.Pseudofunctor.pullHom_ext_of_isPrestack`, separatedness.
* `CategoryTheory.Pseudofunctor.DescentData.Identification.extend`: an identification over a
  covering sieve extends to the maximal sieve.
* `CategoryTheory.Pseudofunctor.DescentData.Identification.existsUnique_isCompatible`: two
  identified objects have a unique compatible comparison between their pullbacks.
* `CategoryTheory.Pseudofunctor.DescentData.Identification.exists_identification_of_essSurj`:
  identifications glue along a family of effective descent.
* `CategoryTheory.Pseudofunctor.DescentData.Identification.isoOfId`: an identification along
  `𝟙 U` is an isomorphism of descent data.
-/

@[expose] public noncomputable section

universe t v' u' v u

namespace CategoryTheory.Pseudofunctor

open Opposite LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C] {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}

/-- The restriction of the section of `F.presheafHom M N` defined by `φ : M ⟶ N` to `W` is the
image of `φ` under the inverse image along `W.hom`. -/
lemma presheafHom_map_presheafHomObjHomEquiv {S : C} {M N : F.obj (.mk (op S))} (φ : M ⟶ N)
    {W : Over S} (g : W ⟶ Over.mk (𝟙 S)) :
    (F.presheafHom M N).map g.op (F.presheafHomObjHomEquiv φ) =
      (F.map W.hom.op.toLoc).toFunctor.map φ := by
  obtain ⟨W, w, rfl⟩ := Over.mk_surjective W
  obtain rfl : g = Over.homMk w := by ext; simpa using Over.w g
  change pullHom (F.presheafHomObjHomEquiv φ) w w w (by simp) (by simp) = _
  rw [pullHom, presheafHomObjHomEquiv_apply]
  simp [F.mapComp'_id_comp_hom_app, F.mapComp'_id_comp_inv_app, ← Functor.map_comp]

/-- The restriction maps of `F.presheafHom M N` are given by `pullHom`. -/
lemma presheafHom_map_eq_pullHom {S : C} {M N : F.obj (.mk (op S))} {W W' : Over S}
    (g : W' ⟶ W) (x : (F.presheafHom M N).obj (op W)) :
    (F.presheafHom M N).map g.op x = pullHom x g.left W'.hom W'.hom (Over.w g) (Over.w g) :=
  rfl

variable {J : GrothendieckTopology C}

/-- **Gluing morphisms in a prestack.** Over a covering sieve `K` of `Y`, a family of morphisms
between the pullbacks of two objects of the fibre over `Y` which is compatible with further
pullback is the family of pullbacks of a unique morphism. -/
theorem existsUnique_map_eq_of_isPrestack [F.IsPrestack J] {Y : C}
    (N₁ N₂ : F.obj (.mk (op Y))) (K : Sieve Y) (hK : K ∈ J Y)
    (χ : ∀ ⦃Y' : C⦄ (s : Y' ⟶ Y), K s →
      ((F.map s.op.toLoc).toFunctor.obj N₁ ⟶ (F.map s.op.toLoc).toFunctor.obj N₂))
    (hχ : ∀ ⦃Y' Y'' : C⦄ (s : Y' ⟶ Y) (hs : K s) (g : Y'' ⟶ Y') (s' : Y'' ⟶ Y)
      (hs' : g ≫ s = s'),
      pullHom (χ s hs) g s' s' hs' hs' = χ s' (hs' ▸ K.downward_closed hs g)) :
    ∃! φ : N₁ ⟶ N₂, ∀ ⦃Y' : C⦄ (s : Y' ⟶ Y) (hs : K s),
      (F.map s.op.toLoc).toFunctor.map φ = χ s hs := by
  let R : Sieve (Over.mk (𝟙 Y)) := (Sieve.overEquiv (Over.mk (𝟙 Y))).symm K
  have hR : R ∈ J.over Y (Over.mk (𝟙 Y)) := by
    rw [GrothendieckTopology.mem_over_iff]
    simpa [R] using hK
  have hmem : ∀ {W : Over Y} (g : W ⟶ Over.mk (𝟙 Y)), R g → K W.hom := by
    intro W g hg
    rw [← show g.left = W.hom by simpa using Over.w g]
    exact hg
  let x : Presieve.FamilyOfElements (F.presheafHom N₁ N₂) R.arrows :=
    fun W g hg ↦ χ W.hom (hmem g hg)
  have hx : x.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ _
    rw [presheafHom_map_eq_pullHom, presheafHom_map_eq_pullHom]
    exact (hχ _ _ _ _ (Over.w g₁)).trans (hχ _ _ _ _ (Over.w g₂)).symm
  obtain ⟨t, ht, ht'⟩ :=
    (isSheaf_iff_isSheaf_of_type _ _).1 (IsPrestack.isSheaf J N₁ N₂) R hR x hx
  refine ⟨F.presheafHomObjHomEquiv.symm t, fun Y' s hs ↦ ?_, fun φ hφ ↦ ?_⟩
  · have h₁ := ht (Over.homMk s : Over.mk s ⟶ Over.mk (𝟙 Y)) hs
    have h₂ := presheafHom_map_presheafHomObjHomEquiv (F.presheafHomObjHomEquiv.symm t)
      (Over.homMk s : Over.mk s ⟶ Over.mk (𝟙 Y))
    rw [Equiv.apply_symm_apply] at h₂
    exact h₂.symm.trans h₁
  · rw [Equiv.eq_symm_apply]
    refine ht' _ (fun W g hg ↦ ?_)
    rw [presheafHom_map_presheafHomObjHomEquiv]
    exact hφ _ _

/-- **Gluing morphisms in a prestack, between pullbacks.** The form of
`existsUnique_map_eq_of_isPrestack` for morphisms `f₁^* M₁ ⟶ f₂^* M₂` between pullbacks of
objects over two different bases, written with `pullHom`. -/
theorem existsUnique_pullHom_eq_of_isPrestack [F.IsPrestack J] {X₁ X₂ Y : C}
    (M₁ : F.obj (.mk (op X₁))) (M₂ : F.obj (.mk (op X₂))) (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂)
    (K : Sieve Y) (hK : K ∈ J Y)
    (χ : ∀ ⦃Y' : C⦄ (s : Y' ⟶ Y), K s →
      ((F.map (s ≫ f₁).op.toLoc).toFunctor.obj M₁ ⟶ (F.map (s ≫ f₂).op.toLoc).toFunctor.obj M₂))
    (hχ : ∀ ⦃Y' Y'' : C⦄ (s : Y' ⟶ Y) (hs : K s) (g : Y'' ⟶ Y'),
      pullHom (χ s hs) g ((g ≫ s) ≫ f₁) ((g ≫ s) ≫ f₂) (by simp) (by simp) =
        χ (g ≫ s) (K.downward_closed hs g)) :
    ∃! φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂,
      ∀ ⦃Y' : C⦄ (s : Y' ⟶ Y) (hs : K s),
        pullHom φ s (s ≫ f₁) (s ≫ f₂) rfl rfl = χ s hs := by
  let χ' : ∀ ⦃Y' : C⦄ (s : Y' ⟶ Y), K s →
      ((F.map s.op.toLoc).toFunctor.obj ((F.map f₁.op.toLoc).toFunctor.obj M₁) ⟶
        (F.map s.op.toLoc).toFunctor.obj ((F.map f₂.op.toLoc).toFunctor.obj M₂)) :=
    fun Y' s hs ↦ (mapCompIso (F := F) (rfl : s ≫ f₁ = s ≫ f₁) M₁).inv ≫ χ s hs ≫
      (mapCompIso (F := F) (rfl : s ≫ f₂ = s ≫ f₂) M₂).hom
  have key : ∀ ⦃Y' : C⦄ (s : Y' ⟶ Y) (hs : K s)
      (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂),
      (F.map s.op.toLoc).toFunctor.map φ = χ' s hs ↔
        pullHom φ s (s ≫ f₁) (s ≫ f₂) rfl rfl = χ s hs := by
    intro Y' s hs φ
    rw [map_eq_pullHom φ s (s ≫ f₁) (s ≫ f₂) rfl rfl]
    change (mapCompIso (F := F) (rfl : s ≫ f₁ = s ≫ f₁) M₁).inv ≫ pullHom φ s _ _ rfl rfl ≫
      (mapCompIso (F := F) (rfl : s ≫ f₂ = s ≫ f₂) M₂).hom =
        (mapCompIso (F := F) (rfl : s ≫ f₁ = s ≫ f₁) M₁).inv ≫ χ s hs ≫
          (mapCompIso (F := F) (rfl : s ≫ f₂ = s ≫ f₂) M₂).hom ↔ _
    rw [Iso.cancel_iso_inv_left, Iso.cancel_iso_hom_right]
  obtain ⟨φ, hφ, hφ'⟩ := existsUnique_map_eq_of_isPrestack (J := J)
    ((F.map f₁.op.toLoc).toFunctor.obj M₁) ((F.map f₂.op.toLoc).toFunctor.obj M₂) K hK χ'
    (by
      intro Y' Y'' s hs g s' hs'
      subst hs'
      simp only [χ']
      rw [Pseudofunctor.pullHom_comp (F := F) _ _ g (g ≫ s) ((g ≫ s) ≫ f₁) (g ≫ s) rfl
          (by simp) rfl,
        Pseudofunctor.pullHom_comp (F := F) _ _ g ((g ≫ s) ≫ f₁) ((g ≫ s) ≫ f₂) (g ≫ s)
          (by simp) (by simp) rfl, hχ s hs g,
        pullHom_inv_eq (F := F) (mapCompIso (F := F) (rfl : s ≫ f₁ = s ≫ f₁) M₁) g (by simp)
          rfl (pullHom_mapCompIso_hom (F := F) _ M₁ g rfl (by simp)),
        pullHom_mapCompIso_hom (F := F) _ M₂ g rfl (by simp)])
  exact ⟨φ, fun Y' s hs ↦ (key s hs φ).1 (hφ s hs),
    fun φ' h ↦ hφ' φ' (fun Y' s hs ↦ (key s hs φ').2 (h s hs))⟩

/-- **Separatedness of morphisms in a prestack.** Two morphisms `f₁^* M₁ ⟶ f₂^* M₂` whose
pullbacks agree over a covering sieve are equal. -/
theorem pullHom_ext_of_isPrestack [F.IsPrestack J] {X₁ X₂ Y : C}
    {M₁ : F.obj (.mk (op X₁))} {M₂ : F.obj (.mk (op X₂))} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    {K : Sieve Y} (hK : K ∈ J Y)
    (φ₁ φ₂ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (h : ∀ ⦃Y' : C⦄ (s : Y' ⟶ Y), K s →
      pullHom φ₁ s (s ≫ f₁) (s ≫ f₂) rfl rfl = pullHom φ₂ s (s ≫ f₁) (s ≫ f₂) rfl rfl) :
    φ₁ = φ₂ :=
  (existsUnique_pullHom_eq_of_isPrestack (J := J) M₁ M₂ f₁ f₂ K hK
    (fun Y' s _ ↦ pullHom φ₁ s (s ≫ f₁) (s ≫ f₂) rfl rfl)
    (fun Y' Y'' s hs g ↦ by rw [pullHom_pullHom])).unique (fun _ _ _ ↦ rfl)
    (fun _ s hs ↦ (h s hs).symm)

/-- The composite of two comparison isomorphisms through a common composite does not depend on
the name of that composite. -/
lemma mapCompIso_inv_comp_hom_congr {X₁ X₂ X₀ Y : C} {a₁ : X₁ ⟶ X₀} {a₂ : X₂ ⟶ X₀}
    {r₁ : Y ⟶ X₁} {r₂ : Y ⟶ X₂} {c c' : Y ⟶ X₀} (h₁ : r₁ ≫ a₁ = c) (h₂ : r₂ ≫ a₂ = c)
    (hc : c = c') (A : F.obj (.mk (op X₀))) :
    (mapCompIso (F := F) h₁ A).inv ≫ (mapCompIso (F := F) h₂ A).hom =
      (mapCompIso (F := F) (h₁.trans hc) A).inv ≫ (mapCompIso (F := F) (h₂.trans hc) A).hom := by
  subst hc
  rfl

/-- **Associativity of the comparison isomorphisms**, in the form of inverse images along a
composite `e ≫ z ≫ a` regrouped as `(e ≫ z) ≫ a`. -/
lemma map_mapCompIso_inv_comp_mapCompIso_inv {X₀ Z₀ E₀ T : C} (a : X₀ ⟶ T) (z : Z₀ ⟶ X₀)
    (e : E₀ ⟶ Z₀) {aZ : Z₀ ⟶ T} {aE : E₀ ⟶ T} {c : E₀ ⟶ X₀} (hZ : z ≫ a = aZ)
    (hE : e ≫ aZ = aE) (hc : e ≫ z = c) (M : F.obj (.mk (op T))) :
    (F.map e.op.toLoc).toFunctor.map (mapCompIso (F := F) hZ M).inv ≫
        (mapCompIso (F := F) hE M).inv =
      (mapCompIso (F := F) hc ((F.map a.op.toLoc).toFunctor.obj M)).inv ≫
        (mapCompIso (F := F) (show c ≫ a = aE by rw [← hc, Category.assoc, hZ, hE]) M).inv :=
  F.mapComp'_inv_whiskerRight_mapComp'₀₂₃_inv_app a.op.toLoc z.op.toLoc e.op.toLoc
    aZ.op.toLoc c.op.toLoc aE.op.toLoc (by rw [← hZ]; rfl) (by rw [← hc]; rfl)
    (by rw [← hE]; rfl) M

/-- The form of `map_mapCompIso_inv_comp_mapCompIso_inv` for the forward isomorphisms. -/
lemma mapCompIso_hom_comp_map_mapCompIso_hom {X₀ Z₀ E₀ T : C} (a : X₀ ⟶ T) (z : Z₀ ⟶ X₀)
    (e : E₀ ⟶ Z₀) {aZ : Z₀ ⟶ T} {aE : E₀ ⟶ T} {c : E₀ ⟶ X₀} (hZ : z ≫ a = aZ)
    (hE : e ≫ aZ = aE) (hc : e ≫ z = c) (M : F.obj (.mk (op T))) :
    (mapCompIso (F := F) hE M).hom ≫
        (F.map e.op.toLoc).toFunctor.map (mapCompIso (F := F) hZ M).hom =
      (mapCompIso (F := F) (show c ≫ a = aE by rw [← hc, Category.assoc, hZ, hE]) M).hom ≫
        (mapCompIso (F := F) hc ((F.map a.op.toLoc).toFunctor.obj M)).hom := by
  have h := map_mapCompIso_inv_comp_mapCompIso_inv (F := F) a z e hZ hE hc M
  have h' : ((F.map e.op.toLoc).toFunctor.mapIso (mapCompIso (F := F) hZ M)).symm ≪≫
      (mapCompIso (F := F) hE M).symm =
      (mapCompIso (F := F) hc ((F.map a.op.toLoc).toFunctor.obj M)).symm ≪≫
        (mapCompIso (F := F) (show c ≫ a = aE by rw [← hc, Category.assoc, hZ, hE]) M).symm :=
    Iso.ext h
  simpa using congrArg Iso.inv h'

/-- The pullback of a morphism depends only on the morphism it is pulled back along. -/
lemma pullHom_congr_left {X₁ X₂ Y Y' : C} {M₁ : F.obj (.mk (op X₁))} {M₂ : F.obj (.mk (op X₂))}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂)
    {g g' : Y' ⟶ Y} (hg : g = g') (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (h₁ : g ≫ f₁ = gf₁)
    (h₂ : g ≫ f₂ = gf₂) (h₁' : g' ≫ f₁ = gf₁) (h₂' : g' ≫ f₂ = gf₂) :
    pullHom φ g gf₁ gf₂ h₁ h₂ = pullHom φ g' gf₁ gf₂ h₁' h₂' := by
  subst hg
  rfl

/-- The identification of the pullbacks of an object along two equal morphisms. -/
def eqHom {X Y : C} {g₁ g₂ : Y ⟶ X} (h : g₁ = g₂) (M : F.obj (.mk (op X))) :
    (F.map g₁.op.toLoc).toFunctor.obj M ⟶ (F.map g₂.op.toLoc).toFunctor.obj M :=
  eqToHom (by rw [h])

/-- The identification of the pullbacks along a morphism and itself is the identity. -/
@[simp]
lemma eqHom_rfl {X Y : C} (g : Y ⟶ X) (h : g = g) (M : F.obj (.mk (op X))) :
    eqHom (F := F) h M = 𝟙 _ :=
  rfl

/-- The composite of two identifications `eqHom` is the identification `eqHom` of the composite
equality. -/
@[reassoc (attr := simp)]
lemma eqHom_comp_eqHom {X Y : C} {g₁ g₂ g₃ : Y ⟶ X} (h₁ : g₁ = g₂) (h₂ : g₂ = g₃)
    (M : F.obj (.mk (op X))) :
    eqHom (F := F) h₁ M ≫ eqHom h₂ M = eqHom (h₁.trans h₂) M := by
  simp [eqHom]

/-- The pullback of an identification `eqHom` is again an identification `eqHom`. -/
lemma pullHom_eqHom {X Y Y' : C} {g₁ g₂ : Y ⟶ X} (h : g₁ = g₂) (M : F.obj (.mk (op X)))
    (t : Y' ⟶ Y) (gf₁ gf₂ : Y' ⟶ X) (h₁ : t ≫ g₁ = gf₁) (h₂ : t ≫ g₂ = gf₂) :
    pullHom (eqHom (F := F) h M) t gf₁ gf₂ h₁ h₂ =
      eqHom (show gf₁ = gf₂ by rw [← h₁, ← h₂, h]) M := by
  subst h h₁ h₂
  exact pullHom_id' (F := F) M t rfl

/-! ### Local identifications with a descent datum -/

section Identification

variable {U : C} {ι : Type t} {X : ι → C} {f : ∀ i, X i ⟶ U}

/-- The morphism `D.hom q f₁ f₂` does not depend on the name given to the common composite `q`. -/
lemma DescentData.hom_congr (D : F.DescentData f) {Y : C} {q q' : Y ⟶ U} (hq : q = q')
    {i₁ i₂ : ι} (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q)
    (hf₁' : f₁ ≫ f i₁ = q') (hf₂' : f₂ ≫ f i₂ = q') :
    D.hom q f₁ f₂ hf₁ hf₂ = D.hom q' f₁ f₂ hf₁' hf₂' := by
  subst hq
  rfl

variable (D : F.DescentData f)

/-- **A local identification of an object with a descent datum.** For a descent datum `D`
relative to a family `f i : X i ⟶ U`, a morphism `a : V ⟶ U`, a sieve `K` on `V` and an object
`y` of the fibre over `V`, this is the data of a morphism `t^* y ⟶ h^* (D.obj i)` for every
member `t` of `K` and every `h : Y ⟶ X i` with `h ≫ f i = t ≫ a`, compatible with pullback and
with the gluing morphisms of `D`.

When `K` is the maximal sieve and `a` is the identity of `U`, this is an isomorphism of `D` with
the descent datum of `y` (`CategoryTheory.Pseudofunctor.DescentData.Identification.isoOfId`). -/
structure DescentData.Identification {V : C} (a : V ⟶ U) (K : Sieve V)
    (y : F.obj (.mk (op V))) where
  /-- The identification over a member of the sieve. -/
  ψ ⦃Y : C⦄ (t : Y ⟶ V) (ht : K t) ⦃i : ι⦄ (h : Y ⟶ X i) (hh : h ≫ f i = t ≫ a) :
    (F.map t.op.toLoc).toFunctor.obj y ⟶ (F.map h.op.toLoc).toFunctor.obj (D.obj i)
  /-- The identifications are compatible with pullback. -/
  pullHom_ψ ⦃Y Y' : C⦄ (g : Y' ⟶ Y) (t : Y ⟶ V) (ht : K t) (t' : Y' ⟶ V) (ht' : g ≫ t = t')
    ⦃i : ι⦄ (h : Y ⟶ X i) (h' : Y' ⟶ X i) (hh' : g ≫ h = h') (hh : h ≫ f i = t ≫ a) :
    pullHom (ψ t ht h hh) g t' h' ht' hh' =
      ψ t' (ht' ▸ K.downward_closed ht g) h'
        (by rw [← hh', ← ht', Category.assoc, hh, Category.assoc])
  /-- The identifications are compatible with the gluing morphisms of `D`. -/
  ψ_hom ⦃Y : C⦄ (t : Y ⟶ V) (ht : K t) ⦃i₁ i₂ : ι⦄ (h₁ : Y ⟶ X i₁) (h₂ : Y ⟶ X i₂)
    (hh₁ : h₁ ≫ f i₁ = t ≫ a) (hh₂ : h₂ ≫ f i₂ = t ≫ a) :
    ψ t ht h₁ hh₁ ≫ D.hom (t ≫ a) h₁ h₂ hh₁ hh₂ = ψ t ht h₂ hh₂

namespace DescentData.Identification

variable {D}

/-- A local identification along `a` is one along any morphism equal to `a`. -/
def ofEq {V : C} {a a' : V ⟶ U} (haa' : a = a') {K : Sieve V} {y : F.obj (.mk (op V))}
    (G : D.Identification a K y) : D.Identification a' K y where
  ψ _ t ht _ h hh := G.ψ t ht h (by rw [hh, haa'])
  pullHom_ψ _ _ g t ht t' ht' _ h h' hh' _ := G.pullHom_ψ g t ht t' ht' h h' hh' _
  ψ_hom _ t ht _ _ h₁ h₂ hh₁ hh₂ := by
    rw [← G.ψ_hom t ht h₁ h₂ (by rw [hh₁, haa']) (by rw [hh₂, haa'])]
    congr 1
    exact D.hom_congr (by rw [haa']) _ _ _ _ _ _

/-- A local identification over `K` restricts to one over a smaller sieve. -/
def mono {V : C} {a : V ⟶ U} {K K' : Sieve V} (hKK' : K' ≤ K) {y : F.obj (.mk (op V))}
    (G : D.Identification a K y) : D.Identification a K' y where
  ψ _ t ht _ h hh := G.ψ t (hKK' _ ht) h hh
  pullHom_ψ _ _ g t ht t' ht' _ h h' hh' hh := G.pullHom_ψ g t (hKK' _ ht) t' ht' h h' hh' hh
  ψ_hom _ t ht _ _ h₁ h₂ hh₁ hh₂ := G.ψ_hom t (hKK' _ ht) h₁ h₂ hh₁ hh₂

/-- Each component of a descent datum is identified with the descent datum, along its member of
the family. -/
def self (i₀ : ι) : D.Identification (f i₀) ⊤ (D.obj i₀) where
  ψ _ t _ _ h hh := D.hom (t ≫ f i₀) t h rfl hh
  pullHom_ψ _ _ g t _ t' ht' _ h h' hh' hh :=
    D.pullHom_hom g (t ≫ f i₀) (t' ≫ f i₀) (by rw [← ht', Category.assoc]) t h rfl hh t' h' ht' hh'
  ψ_hom _ t _ _ _ h₁ h₂ hh₁ hh₂ := D.hom_comp (t ≫ f i₀) t h₁ h₂ rfl hh₁ hh₂

/-- A local identification over the maximal sieve can be precomposed with a morphism of the
fibre. -/
def transport {V : C} {a : V ⟶ U} {y y' : F.obj (.mk (op V))} (G : D.Identification a ⊤ y)
    (φ : y' ⟶ y) : D.Identification a ⊤ y' where
  ψ _ t _ _ h hh := (F.map t.op.toLoc).toFunctor.map φ ≫ G.ψ t trivial h hh
  pullHom_ψ _ _ g t _ t' ht' _ h h' hh' hh := by
    rw [Pseudofunctor.pullHom_comp (F := F) _ _ g t' t' h' ht' ht' hh',
      Pseudofunctor.pullHom_map, G.pullHom_ψ g t trivial t' ht' h h' hh']
  ψ_hom _ t _ _ _ h₁ h₂ hh₁ hh₂ := by
    rw [Category.assoc, G.ψ_hom]

/-- A local identification over the maximal sieve restricts along a morphism `g : V' ⟶ V`. -/
def restrict {V V' : C} {a : V ⟶ U} {y : F.obj (.mk (op V))} (G : D.Identification a ⊤ y)
    (g : V' ⟶ V) : D.Identification (g ≫ a) ⊤ ((F.map g.op.toLoc).toFunctor.obj y) where
  ψ _ t _ _ h hh := (mapCompIso (F := F) (rfl : t ≫ g = t ≫ g) y).inv ≫
    G.ψ (t ≫ g) trivial h (by rw [hh, Category.assoc])
  pullHom_ψ _ _ g' t _ t' ht' _ h h' hh' hh := by
    rw [Pseudofunctor.pullHom_comp (F := F) _ _ g' t' (t' ≫ g) h' ht'
        (by rw [← ht', Category.assoc]) hh',
      pullHom_inv_eq (F := F) (mapCompIso (F := F) (rfl : t ≫ g = t ≫ g) y) g'
        (by rw [← ht', Category.assoc]) ht'
        (pullHom_mapCompIso_hom (F := F) _ y g' ht' (by rw [← ht', Category.assoc])),
      G.pullHom_ψ g' (t ≫ g) trivial (t' ≫ g) (by rw [← ht', Category.assoc]) h h' hh']
  ψ_hom _ t _ _ _ h₁ h₂ hh₁ hh₂ := by
    rw [Category.assoc, ← G.ψ_hom (t ≫ g) trivial h₁ h₂ (by rw [hh₁, Category.assoc])
      (by rw [hh₂, Category.assoc])]
    congr 2
    exact D.hom_congr (by rw [Category.assoc]) _ _ _ _ _ _


section Prestack

variable {J : GrothendieckTopology C} [F.IsPrestack J]

/-- The unique morphism `t^* y ⟶ h^* (D.obj i)` whose pullbacks are the components of `G`. -/
private theorem existsUnique_pullHom_eq_ψ {V : C} {a : V ⟶ U} {K : Sieve V} (hK : K ∈ J V)
    {y : F.obj (.mk (op V))} (G : D.Identification a K y) {Y : C} (t : Y ⟶ V) {i : ι}
    (h : Y ⟶ X i) (hh : h ≫ f i = t ≫ a) :
    ∃! φ : (F.map t.op.toLoc).toFunctor.obj y ⟶ (F.map h.op.toLoc).toFunctor.obj (D.obj i),
      ∀ ⦃Y' : C⦄ (s : Y' ⟶ Y) (hs : (K.pullback t) s),
        pullHom φ s (s ≫ t) (s ≫ h) rfl rfl =
          G.ψ (s ≫ t) hs (s ≫ h) (by rw [Category.assoc, hh, Category.assoc]) :=
  existsUnique_pullHom_eq_of_isPrestack (J := J) y (D.obj i) t h (K.pullback t)
    (J.pullback_stable t hK)
    (fun _ s hs ↦ G.ψ (s ≫ t) hs (s ≫ h) (by rw [Category.assoc, hh, Category.assoc]))
    (fun _ _ s hs g ↦ G.pullHom_ψ g (s ≫ t) hs ((g ≫ s) ≫ t) (by simp) (s ≫ h)
      ((g ≫ s) ≫ h) (by simp) _)

/-- The unique morphism `t^* y ⟶ h^* (D.obj i)` extending a local identification over a covering
sieve `K`. -/
noncomputable def extendψ {V : C} {a : V ⟶ U} {K : Sieve V} (hK : K ∈ J V)
    {y : F.obj (.mk (op V))} (G : D.Identification a K y) {Y : C} (t : Y ⟶ V) {i : ι}
    (h : Y ⟶ X i) (hh : h ≫ f i = t ≫ a) :
    (F.map t.op.toLoc).toFunctor.obj y ⟶ (F.map h.op.toLoc).toFunctor.obj (D.obj i) :=
  (existsUnique_pullHom_eq_of_isPrestack (J := J) y (D.obj i) t h (K.pullback t)
    (J.pullback_stable t hK)
    (fun Y' s hs ↦ G.ψ (s ≫ t) hs (s ≫ h) (by rw [Category.assoc, hh, Category.assoc]))
    (fun Y' Y'' s hs g ↦ G.pullHom_ψ g (s ≫ t) hs ((g ≫ s) ≫ t) (by simp) (s ≫ h)
      ((g ≫ s) ≫ h) (by simp) _)).exists.choose

/-- The pullback of `extendψ hK G t h hh` along a morphism `s` with `s ≫ t` in `K` is the
component of `G` at `s ≫ t`. -/
lemma extendψ_spec {V : C} {a : V ⟶ U} {K : Sieve V} (hK : K ∈ J V)
    {y : F.obj (.mk (op V))} (G : D.Identification a K y) {Y : C} (t : Y ⟶ V) {i : ι}
    (h : Y ⟶ X i) (hh : h ≫ f i = t ≫ a) {Y' : C} (s : Y' ⟶ Y) (s₁ : Y' ⟶ V) (s₂ : Y' ⟶ X i)
    (h₁ : s ≫ t = s₁) (h₂ : s ≫ h = s₂) (hs : K s₁) :
    pullHom (extendψ (J := J) hK G t h hh) s s₁ s₂ h₁ h₂ =
      G.ψ s₁ hs s₂ (by rw [← h₁, ← h₂, Category.assoc, hh, Category.assoc]) := by
  subst h₁ h₂
  exact (existsUnique_pullHom_eq_ψ hK G t h hh).exists.choose_spec s hs

/-- A morphism `t^* y ⟶ h^* (D.obj i)` whose pullback along every `s` with `s ≫ t` in `K` is the
component of `G` at `s ≫ t` is `extendψ hK G t h hh`. -/
lemma extendψ_unique {V : C} {a : V ⟶ U} {K : Sieve V} (hK : K ∈ J V)
    {y : F.obj (.mk (op V))} (G : D.Identification a K y) {Y : C} (t : Y ⟶ V) {i : ι}
    (h : Y ⟶ X i) (hh : h ≫ f i = t ≫ a)
    (φ : (F.map t.op.toLoc).toFunctor.obj y ⟶ (F.map h.op.toLoc).toFunctor.obj (D.obj i))
    (hφ : ∀ ⦃Y' : C⦄ (s : Y' ⟶ Y) (hs : K (s ≫ t)),
      pullHom φ s (s ≫ t) (s ≫ h) rfl rfl =
        G.ψ (s ≫ t) hs (s ≫ h) (by rw [Category.assoc, hh, Category.assoc])) :
    φ = extendψ (J := J) hK G t h hh :=
  (existsUnique_pullHom_eq_ψ hK G t h hh).unique hφ
    (fun _ s hs ↦ extendψ_spec hK G t h hh s (s ≫ t) (s ≫ h) rfl rfl hs)

/-- **Extending a local identification from a covering sieve to the maximal sieve.** -/
noncomputable def extend {V : C} {a : V ⟶ U} {K : Sieve V} (hK : K ∈ J V)
    {y : F.obj (.mk (op V))} (G : D.Identification a K y) : D.Identification a ⊤ y where
  ψ _ t _ _ h hh := extendψ (J := J) hK G t h hh
  pullHom_ψ _ _ g t _ t' ht' _ h h' hh' hh := by
    refine extendψ_unique hK G t' h' _ _ (fun Y'' s hs ↦ ?_)
    rw [pullHom_pullHom]
    exact extendψ_spec hK G t h hh (s ≫ g) (s ≫ t') (s ≫ h')
      (by rw [Category.assoc, ht']) (by rw [Category.assoc, hh']) hs
  ψ_hom _ t _ _ _ h₁ h₂ hh₁ hh₂ := by
    refine extendψ_unique hK G t h₂ _ _ (fun Y'' s hs ↦ ?_)
    rw [Pseudofunctor.pullHom_comp (F := F) _ _ s (s ≫ t) (s ≫ h₁) (s ≫ h₂) rfl rfl rfl,
      extendψ_spec hK G t h₁ hh₁ s (s ≫ t) (s ≫ h₁) rfl rfl hs,
      D.pullHom_hom s (t ≫ a) ((s ≫ t) ≫ a) (by simp) h₁ h₂ hh₁ hh₂ (s ≫ h₁) (s ≫ h₂) rfl rfl,
      G.ψ_hom]

end Prestack

/-- A morphism `f₁^* M₁ ⟶ f₂^* M₂` is *compatible* with identifications of `M₁` and `M₂` with
`D` when its pullbacks intertwine them. -/
def IsCompatible {X₁ X₂ : C} {a₁ : X₁ ⟶ U} {a₂ : X₂ ⟶ U} {M₁ : F.obj (.mk (op X₁))}
    {M₂ : F.obj (.mk (op X₂))} (G₁ : D.Identification a₁ ⊤ M₁) (G₂ : D.Identification a₂ ⊤ M₂)
    {Y : C} (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂)
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂) : Prop :=
  ∀ ⦃Y' : C⦄ (s : Y' ⟶ Y) (s₁ : Y' ⟶ X₁) (s₂ : Y' ⟶ X₂) (h₁ : s ≫ f₁ = s₁) (h₂ : s ≫ f₂ = s₂)
    ⦃i : ι⦄ (h : Y' ⟶ X i) (hh₁ : h ≫ f i = s₁ ≫ a₁) (hh₂ : h ≫ f i = s₂ ≫ a₂),
    pullHom φ s s₁ s₂ h₁ h₂ ≫ G₂.ψ s₂ trivial h hh₂ = G₁.ψ s₁ trivial h hh₁

section Groupoid

variable (hgpd : ∀ (Y : C) (M N : F.obj (.mk (op Y))) (φ : M ⟶ N), IsIso φ)
include hgpd

/-- In a pseudofunctor valued in groupoids, the composite `G₁.ψ s₁ h ≫ (G₂.ψ s₂ h)⁻¹` does not
depend on the choice of `h : Y ⟶ X i` with `h ≫ f i = s₁ ≫ a₁ = s₂ ≫ a₂`. -/
lemma comp_inv_ψ_eq {X₁ X₂ : C} {a₁ : X₁ ⟶ U} {a₂ : X₂ ⟶ U} {M₁ : F.obj (.mk (op X₁))}
    {M₂ : F.obj (.mk (op X₂))} (G₁ : D.Identification a₁ ⊤ M₁) (G₂ : D.Identification a₂ ⊤ M₂)
    {Y : C} (s₁ : Y ⟶ X₁) (s₂ : Y ⟶ X₂) {i i' : ι} (h : Y ⟶ X i) (h' : Y ⟶ X i')
    (hh₁ : h ≫ f i = s₁ ≫ a₁) (hh₂ : h ≫ f i = s₂ ≫ a₂)
    (hh₁' : h' ≫ f i' = s₁ ≫ a₁) (hh₂' : h' ≫ f i' = s₂ ≫ a₂) :
    haveI := hgpd _ _ _ (G₂.ψ s₂ trivial h hh₂)
    haveI := hgpd _ _ _ (G₂.ψ s₂ trivial h' hh₂')
    G₁.ψ s₁ trivial h hh₁ ≫ inv (G₂.ψ s₂ trivial h hh₂) =
      G₁.ψ s₁ trivial h' hh₁' ≫ inv (G₂.ψ s₂ trivial h' hh₂') := by
  have := hgpd _ _ _ (G₂.ψ s₂ trivial h hh₂)
  have := hgpd _ _ _ (G₂.ψ s₂ trivial h' hh₂')
  have := hgpd _ _ _ (D.hom (s₂ ≫ a₂) h h' hh₂ hh₂')
  rw [← G₁.ψ_hom s₁ trivial h h' hh₁ hh₁', ← G₂.ψ_hom s₂ trivial h h' hh₂ hh₂',
    D.hom_congr (show s₁ ≫ a₁ = s₂ ≫ a₂ by rw [← hh₁, hh₂]) h h' hh₁ hh₁' hh₂ hh₂',
    IsIso.inv_comp, Category.assoc, IsIso.hom_inv_id_assoc]

variable {J : GrothendieckTopology C} [F.IsPrestack J]

/-- **Comparison of two identifications.** Two objects identified with `D` have, over any
object mapping to both of their bases compatibly over `U`, a unique compatible morphism between
their pullbacks. -/
theorem existsUnique_isCompatible (hf : Sieve.ofArrows X f ∈ J U) {X₁ X₂ : C} {a₁ : X₁ ⟶ U}
    {a₂ : X₂ ⟶ U} {M₁ : F.obj (.mk (op X₁))} {M₂ : F.obj (.mk (op X₂))}
    (G₁ : D.Identification a₁ ⊤ M₁) (G₂ : D.Identification a₂ ⊤ M₂) {Y : C} (f₁ : Y ⟶ X₁)
    (f₂ : Y ⟶ X₂) (hc : f₁ ≫ a₁ = f₂ ≫ a₂) :
    ∃! φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂,
      IsCompatible G₁ G₂ f₁ f₂ φ := by
  let K : Sieve Y := Sieve.pullback (f₁ ≫ a₁) (Sieve.ofArrows X f)
  have hK : K ∈ J Y := J.pullback_stable _ hf
  have hK' : ∀ ⦃Y' : C⦄ (s : Y' ⟶ Y), K s → Sieve.ofArrows X f (s ≫ f₁ ≫ a₁) :=
    fun _ _ hs ↦ hs
  have fac₁ : ∀ ⦃Y' : C⦄ (s : Y' ⟶ Y) (hs : K s),
      Sieve.ofArrows.h (hK' s hs) ≫ f (Sieve.ofArrows.i (hK' s hs)) = (s ≫ f₁) ≫ a₁ :=
    fun _ s hs ↦ (Sieve.ofArrows.fac (hK' s hs)).trans (Category.assoc _ _ _).symm
  have fac₂ : ∀ ⦃Y' : C⦄ (s : Y' ⟶ Y) (hs : K s),
      Sieve.ofArrows.h (hK' s hs) ≫ f (Sieve.ofArrows.i (hK' s hs)) = (s ≫ f₂) ≫ a₂ :=
    fun _ s hs ↦ (Sieve.ofArrows.fac (hK' s hs)).trans (by rw [hc, Category.assoc])
  let χ : ∀ ⦃Y' : C⦄ (s : Y' ⟶ Y), K s →
      ((F.map (s ≫ f₁).op.toLoc).toFunctor.obj M₁ ⟶
        (F.map (s ≫ f₂).op.toLoc).toFunctor.obj M₂) := fun Y' s hs ↦
    have := hgpd _ _ _ (G₂.ψ (s ≫ f₂) trivial _ (fac₂ s hs))
    G₁.ψ (s ≫ f₁) trivial _ (fac₁ s hs) ≫ inv (G₂.ψ (s ≫ f₂) trivial _ (fac₂ s hs))
  have key : ∀ ⦃Y' : C⦄ (s : Y' ⟶ Y) (hs : K s)
      (φ : (F.map (s ≫ f₁).op.toLoc).toFunctor.obj M₁ ⟶
        (F.map (s ≫ f₂).op.toLoc).toFunctor.obj M₂) ⦃i : ι⦄ (h : Y' ⟶ X i)
      (hh₁ : h ≫ f i = (s ≫ f₁) ≫ a₁) (hh₂ : h ≫ f i = (s ≫ f₂) ≫ a₂),
      φ = χ s hs ↔ φ ≫ G₂.ψ (s ≫ f₂) trivial h hh₂ = G₁.ψ (s ≫ f₁) trivial h hh₁ := by
    intro Y' s hs φ i h hh₁ hh₂
    have := hgpd _ _ _ (G₂.ψ (s ≫ f₂) trivial h hh₂)
    simp only [χ]
    rw [comp_inv_ψ_eq hgpd G₁ G₂ (s ≫ f₁) (s ≫ f₂) _ h (fac₁ s hs) (fac₂ s hs) hh₁ hh₂,
      ← IsIso.eq_comp_inv]
  obtain ⟨φ, hφ, hφ'⟩ := existsUnique_pullHom_eq_of_isPrestack (J := J) M₁ M₂ f₁ f₂ K hK χ
    (by
      intro Y' Y'' s hs g
      have := hgpd _ _ _ (G₂.ψ (s ≫ f₂) trivial _ (fac₂ s hs))
      simp only [χ]
      rw [Pseudofunctor.pullHom_comp (F := F) _ _ g ((g ≫ s) ≫ f₁)
          (g ≫ Sieve.ofArrows.h (hK' s hs)) ((g ≫ s) ≫ f₂) (by simp) rfl (by simp),
        G₁.pullHom_ψ g (s ≫ f₁) trivial ((g ≫ s) ≫ f₁) (by simp) _
          (g ≫ Sieve.ofArrows.h (hK' s hs)) rfl,
        AlgebraicGeometry.pullHom_inv _ g ((g ≫ s) ≫ f₂) (g ≫ Sieve.ofArrows.h (hK' s hs))
          (by simp) rfl]
      simp only [G₂.pullHom_ψ g (s ≫ f₂) trivial ((g ≫ s) ≫ f₂) (by simp) _
        (g ≫ Sieve.ofArrows.h (hK' s hs)) rfl]
      exact comp_inv_ψ_eq hgpd G₁ G₂ _ _ _ _ _ _ _ _)
  refine ⟨φ, ?_, fun φ' hφ'' ↦ hφ' φ' (fun Y' s hs ↦ ?_)⟩
  · intro Y' s s₁ s₂ h₁ h₂ i h hh₁ hh₂
    subst h₁ h₂
    have hs : K s := by
      change Sieve.ofArrows X f (s ≫ f₁ ≫ a₁)
      rw [← Category.assoc, ← hh₁]
      exact Sieve.downward_closed _ (Sieve.ofArrows_mk X f i) h
    exact (key s hs _ h hh₁ hh₂).1 (hφ s hs)
  · exact (key s hs _ _ (fac₁ s hs) (fac₂ s hs)).2
      (hφ'' s (s ≫ f₁) (s ≫ f₂) rfl rfl _ (fac₁ s hs) (fac₂ s hs))

/-- The compatible morphism of `existsUnique_isCompatible`. -/
noncomputable def compatibleHom (hf : Sieve.ofArrows X f ∈ J U) {X₁ X₂ : C} {a₁ : X₁ ⟶ U}
    {a₂ : X₂ ⟶ U} {M₁ : F.obj (.mk (op X₁))} {M₂ : F.obj (.mk (op X₂))}
    (G₁ : D.Identification a₁ ⊤ M₁) (G₂ : D.Identification a₂ ⊤ M₂) {Y : C} (f₁ : Y ⟶ X₁)
    (f₂ : Y ⟶ X₂) (hc : f₁ ≫ a₁ = f₂ ≫ a₂) :
    (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂ :=
  (existsUnique_isCompatible hgpd (J := J) hf G₁ G₂ f₁ f₂ hc).exists.choose

/-- The morphism `compatibleHom` is compatible with the identifications `G₁` and `G₂`. -/
lemma isCompatible_compatibleHom (hf : Sieve.ofArrows X f ∈ J U) {X₁ X₂ : C} {a₁ : X₁ ⟶ U}
    {a₂ : X₂ ⟶ U} {M₁ : F.obj (.mk (op X₁))} {M₂ : F.obj (.mk (op X₂))}
    (G₁ : D.Identification a₁ ⊤ M₁) (G₂ : D.Identification a₂ ⊤ M₂) {Y : C} (f₁ : Y ⟶ X₁)
    (f₂ : Y ⟶ X₂) (hc : f₁ ≫ a₁ = f₂ ≫ a₂) :
    IsCompatible G₁ G₂ f₁ f₂ (compatibleHom hgpd (J := J) hf G₁ G₂ f₁ f₂ hc) :=
  (existsUnique_isCompatible hgpd (J := J) hf G₁ G₂ f₁ f₂ hc).exists.choose_spec

/-- A morphism compatible with the identifications `G₁` and `G₂` is `compatibleHom`. -/
lemma eq_compatibleHom (hf : Sieve.ofArrows X f ∈ J U) {X₁ X₂ : C} {a₁ : X₁ ⟶ U}
    {a₂ : X₂ ⟶ U} {M₁ : F.obj (.mk (op X₁))} {M₂ : F.obj (.mk (op X₂))}
    (G₁ : D.Identification a₁ ⊤ M₁) (G₂ : D.Identification a₂ ⊤ M₂) {Y : C} (f₁ : Y ⟶ X₁)
    (f₂ : Y ⟶ X₂) (hc : f₁ ≫ a₁ = f₂ ≫ a₂)
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (hφ : IsCompatible G₁ G₂ f₁ f₂ φ) :
    φ = compatibleHom hgpd (J := J) hf G₁ G₂ f₁ f₂ hc :=
  (existsUnique_isCompatible hgpd (J := J) hf G₁ G₂ f₁ f₂ hc).unique hφ
    (isCompatible_compatibleHom hgpd hf G₁ G₂ f₁ f₂ hc)

omit hgpd in
/-- The pullback of a morphism compatible with the identifications `G₁` and `G₂` is compatible
with them. -/
lemma isCompatible_pullHom {X₁ X₂ : C} {a₁ : X₁ ⟶ U} {a₂ : X₂ ⟶ U}
    {M₁ : F.obj (.mk (op X₁))} {M₂ : F.obj (.mk (op X₂))}
    {G₁ : D.Identification a₁ ⊤ M₁} {G₂ : D.Identification a₂ ⊤ M₂} {Y : C} {f₁ : Y ⟶ X₁}
    {f₂ : Y ⟶ X₂}
    {φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂}
    (hφ : IsCompatible G₁ G₂ f₁ f₂ φ) {Y' : C} (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    IsCompatible G₁ G₂ gf₁ gf₂ (pullHom φ g gf₁ gf₂ hgf₁ hgf₂) := by
  intro Y'' s s₁ s₂ h₁ h₂ i h hh₁ hh₂
  rw [pullHom_pullHom]
  exact hφ (s ≫ g) s₁ s₂ (by rw [Category.assoc, hgf₁, h₁]) (by rw [Category.assoc, hgf₂, h₂])
    h hh₁ hh₂

/-- **The descent datum glued from identifications.** Objects `y k` over the members of a
family `v k : W k ⟶ V`, each identified with `D` along `v k ≫ a`, form a descent datum relative
to `v`: its gluing morphisms are the compatible morphisms of `existsUnique_isCompatible`. -/
noncomputable def glueDescentData (hf : Sieve.ofArrows X f ∈ J U) {V : C} (a : V ⟶ U)
    {κ : Type*} {W : κ → C} (v : ∀ k, W k ⟶ V) (y : ∀ k, F.obj (.mk (op (W k))))
    (G : ∀ k, D.Identification (v k ≫ a) ⊤ (y k)) : F.DescentData v where
  obj := y
  hom _ q k₁ k₂ f₁ f₂ hf₁ hf₂ := compatibleHom hgpd (J := J) hf (G k₁) (G k₂) f₁ f₂
    (by rw [← Category.assoc, hf₁, ← Category.assoc, hf₂])
  pullHom_hom _ _ g q q' hq k₁ k₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ :=
    eq_compatibleHom hgpd hf _ _ _ _ _ _
      (isCompatible_pullHom (isCompatible_compatibleHom hgpd hf _ _ _ _ _) g gf₁ gf₂ hgf₁
        hgf₂)
  hom_self _ q k g hg := by
    refine (eq_compatibleHom hgpd hf _ _ _ _ _ _ (fun Y' s s₁ s₂ h₁ h₂ i h hh₁ hh₂ ↦ ?_)).symm
    subst h₁ h₂
    rw [pullHom_id']
    exact Category.id_comp _
  hom_comp _ q k₁ k₂ k₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ := by
    refine eq_compatibleHom hgpd hf _ _ _ _ _ _ (fun Y' s s₁ s₃ h₁ h₃ i h hh₁ hh₃ ↦ ?_)
    have hh₂ : h ≫ f i = (s ≫ f₂) ≫ v k₂ ≫ a := by
      rw [hh₃, ← h₃]
      simp only [Category.assoc, reassoc_of% hf₃, reassoc_of% hf₂]
    rw [Pseudofunctor.pullHom_comp (F := F) _ _ s s₁ (s ≫ f₂) s₃ h₁ rfl h₃, Category.assoc,
      isCompatible_compatibleHom hgpd hf _ _ _ _ _ s (s ≫ f₂) s₃ rfl h₃ h hh₂ hh₃,
      isCompatible_compatibleHom hgpd hf _ _ _ _ _ s s₁ (s ≫ f₂) h₁ rfl h hh₁ hh₂]


section OfIso

variable (hf : Sieve.ofArrows X f ∈ J U) {V : C} {a : V ⟶ U} {κ : Type*} {W : κ → C}
  {v : ∀ k, W k ⟶ V} {y : ∀ k, F.obj (.mk (op (W k)))}
  {G : ∀ k, D.Identification (v k ≫ a) ⊤ (y k)} {y' : F.obj (.mk (op V))}
  (θ : (F.toDescentData v).obj y' ≅ glueDescentData hgpd (J := J) hf a v y G)

/-- The components of an isomorphism with the glued descent datum. -/
noncomputable def isoComponent (k : κ) : (F.map (v k).op.toLoc).toFunctor.obj y' ⟶ y k :=
  θ.hom.hom k

/-- The components `isoComponent` intertwine the gluing morphisms of the descent datum of `y'`
with those of the glued descent datum. -/
lemma isoComponent_comm {Y : C} (t : Y ⟶ V) {k₁ k₂ : κ} (r₁ : Y ⟶ W k₁) (r₂ : Y ⟶ W k₂)
    (hr₁ : r₁ ≫ v k₁ = t) (hr₂ : r₂ ≫ v k₂ = t) :
    (F.map r₁.op.toLoc).toFunctor.map (isoComponent hgpd hf θ k₁) ≫
        compatibleHom hgpd (J := J) hf (G k₁) (G k₂) r₁ r₂
          (by rw [← Category.assoc, hr₁, ← Category.assoc, hr₂]) =
      ((mapCompIso (F := F) hr₁ y').inv ≫ (mapCompIso (F := F) hr₂ y').hom) ≫
        (F.map r₂.op.toLoc).toFunctor.map (isoComponent hgpd hf θ k₂) :=
  θ.hom.comm t r₁ r₂ hr₁ hr₂

/-- For `r₁ ≫ v k₁ = r₂ ≫ v k₂ = t`, the composites of the components `isoComponent` with the
identifications `G k₁` and `G k₂` agree as morphisms out of `t^* y'`. -/
lemma ofIso_aux {Y : C} (t : Y ⟶ V) {k₁ k₂ : κ} (r₁ : Y ⟶ W k₁) (r₂ : Y ⟶ W k₂)
    (hr₁ : r₁ ≫ v k₁ = t) (hr₂ : r₂ ≫ v k₂ = t) {i : ι} (h : Y ⟶ X i)
    (hh₁ : h ≫ f i = r₁ ≫ v k₁ ≫ a) (hh₂ : h ≫ f i = r₂ ≫ v k₂ ≫ a) :
    (mapCompIso (F := F) hr₁ y').hom ≫
        (F.map r₁.op.toLoc).toFunctor.map (isoComponent hgpd hf θ k₁) ≫
        (G k₁).ψ r₁ trivial h hh₁ =
      (mapCompIso (F := F) hr₂ y').hom ≫
        (F.map r₂.op.toLoc).toFunctor.map (isoComponent hgpd hf θ k₂) ≫
        (G k₂).ψ r₂ trivial h hh₂ := by
  have hcomp := isCompatible_compatibleHom hgpd (J := J) hf (G k₁) (G k₂) r₁ r₂
    (by rw [← Category.assoc, hr₁, ← Category.assoc, hr₂]) (𝟙 Y) r₁ r₂ (by simp) (by simp) h
    hh₁ hh₂
  rw [pullHom_id] at hcomp
  rw [← hcomp, reassoc_of% (isoComponent_comm hgpd hf θ t r₁ r₂ hr₁ hr₂)]
  simp

/-- The identification of `y'` with `D` over the sieve generated by `v`, read off an
isomorphism of the descent datum of `y'` with the glued descent datum. -/
noncomputable def ofIsoOnSieve : D.Identification a (Sieve.ofArrows W v) y' where
  ψ _ t ht _ h hh := (mapCompIso (F := F) (Sieve.ofArrows.fac ht) y').hom ≫
    (F.map (Sieve.ofArrows.h ht).op.toLoc).toFunctor.map
      (isoComponent hgpd hf θ (Sieve.ofArrows.i ht)) ≫
      (G (Sieve.ofArrows.i ht)).ψ (Sieve.ofArrows.h ht) trivial h
        (hh.trans (Sieve.ofArrows.fac_assoc ht a).symm)
  pullHom_ψ _ _ g t ht t' ht' _ h h' hh' hh := by
    rw [Pseudofunctor.pullHom_comp (F := F) _ _ g t' (g ≫ Sieve.ofArrows.h ht) h' ht' rfl hh',
      Pseudofunctor.pullHom_comp (F := F) _ _ g (g ≫ Sieve.ofArrows.h ht)
        (g ≫ Sieve.ofArrows.h ht) h' rfl rfl hh',
      pullHom_mapCompIso_hom (F := F) _ y' g rfl ht', Pseudofunctor.pullHom_map,
      (G _).pullHom_ψ g _ trivial _ rfl h h' hh']
    exact ofIso_aux hgpd hf θ t' _ _ _ _ h' _ _
  ψ_hom _ t ht _ _ h₁ h₂ hh₁ hh₂ := by
    have e := (G (Sieve.ofArrows.i ht)).ψ_hom (Sieve.ofArrows.h ht) trivial h₁ h₂
      (hh₁.trans (Sieve.ofArrows.fac_assoc ht a).symm)
      (hh₂.trans (Sieve.ofArrows.fac_assoc ht a).symm)
    rw [D.hom_congr (Sieve.ofArrows.fac_assoc ht a) h₁ h₂ _ _ hh₁ hh₂] at e
    simp only [Category.assoc, e]

/-- **Effectivity of the glued descent datum gives an identification.** -/
noncomputable def ofIso (hv : Sieve.ofArrows W v ∈ J V) : D.Identification a ⊤ y' :=
  (ofIsoOnSieve hgpd hf θ).extend hv

end OfIso

/-- **Local identifications glue along a family of effective descent.** -/
theorem exists_identification_of_essSurj (hf : Sieve.ofArrows X f ∈ J U) {V : C} (a : V ⟶ U)
    {κ : Type*} {W : κ → C} (v : ∀ k, W k ⟶ V) (hv : Sieve.ofArrows W v ∈ J V)
    [(F.toDescentData v).EssSurj] (y : ∀ k, F.obj (.mk (op (W k))))
    (G : ∀ k, D.Identification (v k ≫ a) ⊤ (y k)) :
    ∃ y' : F.obj (.mk (op V)), Nonempty (D.Identification a ⊤ y') :=
  ⟨(F.toDescentData v).objPreimage (glueDescentData hgpd (J := J) hf a v y G),
    ⟨ofIso hgpd hf ((F.toDescentData v).objObjPreimageIso _) hv⟩⟩

end Groupoid

section Id

/-- The unit isomorphism `(𝟙 Z)^* M ⟶ M` of the pseudofunctor, with its source written as the
pullback along `𝟙 Z`. -/
noncomputable def unitHom {Z : C} (M : F.obj (.mk (op Z))) :
    (F.map (𝟙 Z).op.toLoc).toFunctor.obj M ⟶ M :=
  (F.mapId' (𝟙 Z).op.toLoc).hom.toNatTrans.app M

/-- The comparison isomorphism `g^* M ⟶ g^* (𝟙 Z)^* M` followed by the pullback of `unitHom M`
along `g` is the identity. -/
lemma mapComp'_hom_map_unitHom {Z Y : C} (M : F.obj (.mk (op Z))) (g : Y ⟶ Z)
    (hg : (𝟙 Z).op.toLoc ≫ g.op.toLoc = g.op.toLoc) :
    (F.mapComp' (𝟙 Z).op.toLoc g.op.toLoc g.op.toLoc hg).hom.toNatTrans.app M ≫
      (F.map g.op.toLoc).toFunctor.map (unitHom (F := F) M) = 𝟙 _ := by
  simp [unitHom, mapId'_eq_mapId, F.mapComp'_id_comp_hom_app, ← Functor.map_comp]

variable {y : F.obj (.mk (op U))} (G : D.Identification (𝟙 U) ⊤ y)

/-- The component at `i` of the isomorphism attached to an identification along `𝟙 U`. -/
noncomputable def isoOfIdComponent (i : ι) :
    (F.map (f i).op.toLoc).toFunctor.obj y ⟶ D.obj i :=
  G.ψ (f i) trivial (𝟙 (X i)) (by simp) ≫ unitHom (D.obj i)

/-- The pullback along `g : Y ⟶ X i` of the component `isoOfIdComponent G i` is the component of
`G` at `q = g ≫ f i`, up to the comparison isomorphism. -/
lemma map_isoOfIdComponent {Y : C} (q : Y ⟶ U) {i : ι} (g : Y ⟶ X i) (hg : g ≫ f i = q) :
    (F.map g.op.toLoc).toFunctor.map (isoOfIdComponent G i) =
      (mapCompIso (F := F) hg y).inv ≫ G.ψ q trivial g (by simp [hg]) := by
  rw [isoOfIdComponent, Functor.map_comp, map_eq_pullHom _ g q g hg (by simp),
    G.pullHom_ψ g (f i) trivial q hg (𝟙 (X i)) g (by simp), Category.assoc, Category.assoc,
    mapComp'_hom_map_unitHom, Category.comp_id]
  rfl

/-- **An identification along the identity is an isomorphism of descent data.** -/
noncomputable def isoOfId (hgpd : ∀ (Y : C) (M N : F.obj (.mk (op Y))) (φ : M ⟶ N), IsIso φ) :
    (F.toDescentData f).obj y ≅ D :=
  DescentData.isoMk (fun i ↦ @asIso _ _ _ _ (isoOfIdComponent G i) (hgpd _ _ _ _)) (by
    intro Y q i₁ i₂ f₁ f₂ hf₁ hf₂
    change (F.map f₁.op.toLoc).toFunctor.map (isoOfIdComponent G i₁) ≫ _ =
      ((mapCompIso (F := F) hf₁ y).inv ≫ (mapCompIso (F := F) hf₂ y).hom) ≫
        (F.map f₂.op.toLoc).toFunctor.map (isoOfIdComponent G i₂)
    rw [map_isoOfIdComponent G q f₁ hf₁, map_isoOfIdComponent G q f₂ hf₂, Category.assoc,
      ← G.ψ_hom q trivial f₁ f₂ (by simp [hf₁]) (by simp [hf₂]),
      D.hom_congr (Category.comp_id q).symm f₁ f₂ hf₁ hf₂ (by simp [hf₁]) (by simp [hf₂])]
    simp)

end Id



end DescentData.Identification

end Identification

end CategoryTheory.Pseudofunctor
