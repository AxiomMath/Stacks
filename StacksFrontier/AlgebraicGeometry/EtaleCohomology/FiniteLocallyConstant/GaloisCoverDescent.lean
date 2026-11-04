module

public import Mathlib.CategoryTheory.Sites.SheafHom
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeContinuous
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DirectImageSystem
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantModuleSheafIrreducibleSectionsRing
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExamplesSheaves.ConstantModuleSheafSections
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCoverSheets

/-!
# Descent of sheaves of modules along a Galois covering

Let `X` be a scheme and let `A ⟶ X` be an étale covering on which a group `H` acts by
`X`-automorphisms in such a way that `A` is a Galois covering of `X` with group `H`: two
`X`-morphisms into `A` differ, locally on their source, by a unique element of `H`. For a
`Λ`-module `N` with an action of `H`, this file constructs the sheaf of `Λ`-modules `D(N)` on the
small étale site of `X` whose sections over an étale `X`-scheme `W` are the locally constant
`H`-equivariant maps `W ×_X A → N`, and shows that its restriction to `A` is the constant sheaf
`N̲`. This is the inverse construction of Stacks Tag 0GIY, `f_* Z ⊗_{Z[G]} M`, written as the
sheaf of equivariant locally constant maps.

## Main definitions

* `AlgebraicGeometry.EtaleGaloisCovering` — a Galois covering of `X` with group `H`.
* `AlgebraicGeometry.EtaleGaloisCovering.descentSheaf` — the sheaf `D(N)`.

## Main results

* `AlgebraicGeometry.EtaleGaloisCovering.isSheaf_descentPresheaf` — `D(N)` is a sheaf.

## References

* [Stacks Project, Tag 0GIY](https://stacks.math.columbia.edu/tag/0GIY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u r w v

namespace AlgebraicGeometry

/-- **A Galois covering of `X` with group `H`.** An étale `X`-scheme `A`, irreducible and
surjective over `X`, with an action of `H` by `X`-automorphisms, such that two `X`-morphisms
into `A` from any scheme agree, near every point, after composing one of them with the action of
an element of `H`, and such that this element is unique on a nonempty scheme. -/
structure EtaleGaloisCovering (X : Scheme.{u}) (H : Type w) [Group H] where
  /-- The covering, as an object of the small étale site. -/
  cover : X.Etale
  /-- The action of the group on the covering. -/
  act : H → (cover.left ⟶ cover.left)
  /-- Each element of the group acts by an `X`-morphism. -/
  act_comp_hom (h : H) : act h ≫ cover.hom = cover.hom
  /-- The neutral element acts as the identity. -/
  act_one : act 1 = 𝟙 _
  /-- The action is compatible with multiplication. -/
  act_mul (h h' : H) : act (h * h') = act h' ≫ act h
  /-- The covering is surjective onto `X`. -/
  surjective : Function.Surjective cover.hom.base
  /-- The underlying space of the covering is irreducible. -/
  irreducibleSpace : IrreducibleSpace cover.left
  /-- Two `X`-morphisms into the covering agree near every point after composing one of them
  with the action of some element of the group. -/
  exists_mem_agreeLocus {W : Scheme.{u}} (a b : W ⟶ cover.left)
    (hab : a ≫ cover.hom = b ≫ cover.hom) (w : W) :
    ∃ (h : H) (hw : (a ≫ act h) ≫ cover.hom = b ≫ cover.hom),
      w ∈ Scheme.Hom.agreeLocus cover.hom _ _ hw
  /-- On a nonempty scheme, a morphism into the covering determines the acting element. -/
  eq_of_comp_eq {V : Scheme.{u}} [Nonempty V] (c : V ⟶ cover.left) {h h' : H}
    (hc : c ≫ act h = c ≫ act h') : h = h'

namespace EtaleGaloisCovering

variable {X : Scheme.{u}} {H : Type w} [Group H] (G : EtaleGaloisCovering X H)

attribute [instance] irreducibleSpace

/-- Each element of the group acts by an `X`-morphism. -/
@[reassoc (attr := simp)]
theorem act_comp_hom' (h : H) : G.act h ≫ G.cover.hom = G.cover.hom :=
  G.act_comp_hom h

/-- The action of `h`, as an endomorphism of the covering in the small étale site. -/
def actHom (h : H) : G.cover ⟶ G.cover :=
  MorphismProperty.Over.homMk (G.act h) (G.act_comp_hom h)

/-- The underlying morphism of schemes of `actHom h` is the action of `h`. -/
@[simp]
theorem actHom_left (h : H) : (G.actHom h).left = G.act h :=
  rfl

/-- The fibre product `W ×_X A` of an étale `X`-scheme with the covering. -/
abbrev fiberProd (W : X.Etale) : Scheme.{u} :=
  Limits.pullback W.hom G.cover.hom

/-- The action of `h` on the fibre product `W ×_X A`, through the second factor. -/
def pullbackAct (W : X.Etale) (h : H) : G.fiberProd W ⟶ G.fiberProd W :=
  pullback.map _ _ _ _ (𝟙 _) (G.act h) (𝟙 _) (by simp) (by simp)

/-- The action on `W ×_X A` commutes with the first projection. -/
@[reassoc (attr := simp)]
theorem pullbackAct_fst (W : X.Etale) (h : H) :
    G.pullbackAct W h ≫ pullback.fst _ _ = pullback.fst _ _ :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

/-- The action on `W ×_X A` is the action on `A` through the second projection. -/
@[reassoc (attr := simp)]
theorem pullbackAct_snd (W : X.Etale) (h : H) :
    G.pullbackAct W h ≫ pullback.snd _ _ = pullback.snd _ _ ≫ G.act h :=
  pullback.lift_snd _ _ _

/-- The action on `W ×_X A` is compatible with multiplication. -/
theorem pullbackAct_mul (W : X.Etale) (h h' : H) :
    G.pullbackAct W (h * h') = G.pullbackAct W h' ≫ G.pullbackAct W h := by
  apply pullback.hom_ext <;> simp [G.act_mul]

/-- The neutral element acts on `W ×_X A` as the identity. -/
theorem pullbackAct_one (W : X.Etale) : G.pullbackAct W 1 = 𝟙 _ := by
  apply pullback.hom_ext <;> simp [G.act_one]

/-- The map `W' ×_X A ⟶ W ×_X A` induced by a morphism `W' ⟶ W` of the small étale site. -/
def pullbackMap {W W' : X.Etale} (g : W' ⟶ W) : G.fiberProd W' ⟶ G.fiberProd W :=
  pullback.map _ _ _ _ g.left (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id]; exact (MorphismProperty.Over.w g).symm) (by simp)

/-- The first projection of `pullbackMap g` is `g` on the first factor. -/
@[reassoc (attr := simp)]
theorem pullbackMap_fst {W W' : X.Etale} (g : W' ⟶ W) :
    G.pullbackMap g ≫ pullback.fst _ _ = pullback.fst _ _ ≫ g.left :=
  pullback.lift_fst _ _ _

/-- The map `pullbackMap g` commutes with the second projection. -/
@[reassoc (attr := simp)]
theorem pullbackMap_snd {W W' : X.Etale} (g : W' ⟶ W) :
    G.pullbackMap g ≫ pullback.snd _ _ = pullback.snd _ _ :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- The map `pullbackMap g` is equivariant for the action of the group. -/
@[reassoc]
theorem pullbackMap_pullbackAct {W W' : X.Etale} (g : W' ⟶ W) (h : H) :
    G.pullbackMap g ≫ G.pullbackAct W h = G.pullbackAct W' h ≫ G.pullbackMap g := by
  apply pullback.hom_ext <;> simp

/-- The identity of `W` induces the identity of `W ×_X A`. -/
theorem pullbackMap_id (W : X.Etale) : G.pullbackMap (𝟙 W) = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [pullbackMap_fst, Category.id_comp]
    exact Category.comp_id _
  · simp

/-- The map induced on fibre products by a composite is the composite of the induced maps. -/
theorem pullbackMap_comp {W W' W'' : X.Etale} (g : W' ⟶ W) (g' : W'' ⟶ W') :
    G.pullbackMap (g' ≫ g) = G.pullbackMap g' ≫ G.pullbackMap g := by
  apply pullback.hom_ext
  · rw [pullbackMap_fst, Category.assoc, pullbackMap_fst, pullbackMap_fst_assoc]
    rfl
  · simp

/-! ### The fibre product of an object over the covering with the covering -/

section Graph

/-- The graph `y ↦ (y, w y)` of the structure morphism `w : T ⟶ A` of an object `T` over the
covering, as a section of the first projection `T ×_X A ⟶ T`. -/
def graph (T : Over G.cover) : T.left.left ⟶ G.fiberProd T.left :=
  pullback.lift (𝟙 _) T.hom.left (by
    rw [Category.id_comp]
    exact (MorphismProperty.Over.w T.hom).symm)

/-- The graph is a section of the first projection. -/
@[reassoc (attr := simp)]
theorem graph_fst (T : Over G.cover) : G.graph T ≫ pullback.fst _ _ = 𝟙 _ :=
  pullback.lift_fst _ _ _

/-- The second projection of the graph is the structure morphism `T ⟶ A`. -/
@[reassoc (attr := simp)]
theorem graph_snd (T : Over G.cover) : G.graph T ≫ pullback.snd _ _ = T.hom.left :=
  pullback.lift_snd _ _ _

/-- The graph is natural in the object `T` over the covering. -/
@[reassoc]
theorem graph_naturality {T T' : Over G.cover} (k : T' ⟶ T) :
    k.left.left ≫ G.graph T = G.graph T' ≫ G.pullbackMap k.left := by
  apply pullback.hom_ext
  · simp
  · rw [Category.assoc, graph_snd, Category.assoc, pullbackMap_snd, graph_snd]
    exact congrArg (fun m : T'.left ⟶ G.cover ↦ m.left) (CategoryTheory.Over.w k)

variable (T : Over G.cover)

/-- On `T ×_X A`, the first projection followed by `T ⟶ A` and the second projection have the
same composite to `X`. -/
theorem fst_comp_comp_hom :
    (pullback.fst T.left.hom G.cover.hom ≫ T.hom.left) ≫ G.cover.hom =
      pullback.snd T.left.hom G.cover.hom ≫ G.cover.hom := by
  rw [Category.assoc, MorphismProperty.Over.w T.hom, pullback.condition]

/-- The locus in `T ×_X A` where the second projection is the first one followed by the
structure morphism and the action of `h`. -/
abbrev sheet (h : H) : (G.fiberProd T.left).Opens :=
  Scheme.Hom.agreeLocus G.cover.hom ((pullback.fst _ _ ≫ T.hom.left) ≫ G.act h)
    (pullback.snd _ _) (by rw [Category.assoc, G.act_comp_hom', G.fst_comp_comp_hom])

/-- Every point of `T ×_X A` lies on some sheet. -/
theorem exists_mem_sheet (z : G.fiberProd T.left) : ∃ h, z ∈ G.sheet T h := by
  obtain ⟨h, hw, hz⟩ := G.exists_mem_agreeLocus _ _ (G.fst_comp_comp_hom T) z
  exact ⟨h, hz⟩

/-- On its sheet, the second projection is the first one followed by the structure morphism and
the action of `h`. -/
theorem sheet_ι_comp (h : H) :
    (G.sheet T h).ι ≫ (pullback.fst _ _ ≫ T.hom.left) ≫ G.act h =
      (G.sheet T h).ι ≫ pullback.snd _ _ :=
  Scheme.Hom.agreeLocus_ι_comp G.cover.hom _ _ _

/-- **The sheets are disjoint.** -/
theorem eq_of_mem_sheet {z : G.fiberProd T.left} {h h' : H} (hz : z ∈ G.sheet T h)
    (hz' : z ∈ G.sheet T h') : h = h' := by
  let O : (G.fiberProd T.left).Opens := G.sheet T h ⊓ G.sheet T h'
  have : Nonempty O := ⟨⟨z, hz, hz'⟩⟩
  let j₁ : (O : Scheme.{u}) ⟶ G.sheet T h := (G.fiberProd T.left).homOfLE inf_le_left
  let j₂ : (O : Scheme.{u}) ⟶ G.sheet T h' := (G.fiberProd T.left).homOfLE inf_le_right
  have hj : j₁ ≫ (G.sheet T h).ι = j₂ ≫ (G.sheet T h').ι := by
    simp only [j₁, j₂, Scheme.homOfLE_ι]
  refine G.eq_of_comp_eq (j₁ ≫ (G.sheet T h).ι ≫ pullback.fst _ _ ≫ T.hom.left) ?_
  have h₁ := congrArg (j₁ ≫ ·) (G.sheet_ι_comp T h)
  have h₂ := congrArg (j₂ ≫ ·) (G.sheet_ι_comp T h')
  have hj' := reassoc_of% hj
  simp only [Category.assoc] at h₁ h₂ ⊢
  rw [h₁, hj', ← h₂]
  exact (hj' _).symm

end Graph


/-! ### The descent sheaf -/

section Descent

variable (Λ : Type r) [Ring Λ] (N : Type v) [AddCommGroup N] [Module Λ N]
  (ρ : H →* Module.End Λ N)

/-- The `H`-equivariant locally constant maps `W ×_X A → N`. -/
def equivariantMaps (W : X.Etale) : Submodule Λ (LocallyConstant (G.fiberProd W) N)
    where
  carrier := {f | ∀ (h : H) (z : G.fiberProd W),
    f ((G.pullbackAct W h).base z) = ρ h (f z)}
  add_mem' {f g} hf hg h z := by
    simp only [LocallyConstant.coe_add, Pi.add_apply, hf h z, hg h z, map_add]
  zero_mem' h z := by simp
  smul_mem' c f hf h z := by
    simp only [LocallyConstant.coe_smul, Pi.smul_apply, hf h z, map_smul]

variable {Λ N ρ} in
/-- A locally constant map `W ×_X A → N` is equivariant when it intertwines the two actions. -/
theorem mem_equivariantMaps_iff {W : X.Etale}
    (f : LocallyConstant (G.fiberProd W) N) :
    f ∈ G.equivariantMaps Λ N ρ W ↔ ∀ (h : H) (z : G.fiberProd W),
      f ((G.pullbackAct W h).base z) = ρ h (f z) :=
  Iff.rfl

variable {Λ N ρ} in
/-- Restriction of an equivariant locally constant map along `W' ⟶ W` is equivariant. -/
theorem comap_mem_equivariantMaps {W W' : X.Etale} (g : W' ⟶ W)
    {f : LocallyConstant (G.fiberProd W) N} (hf : f ∈ G.equivariantMaps Λ N ρ W) :
    LocallyConstant.comapₗ Λ (G.pullbackMap g).base.hom f ∈ G.equivariantMaps Λ N ρ W' := by
  intro h z
  show f ((G.pullbackMap g).base ((G.pullbackAct W' h).base z)) =
    ρ h (f ((G.pullbackMap g).base z))
  rw [← Scheme.Hom.comp_apply, ← G.pullbackMap_pullbackAct, Scheme.Hom.comp_apply, hf]

/-- **The descent presheaf `D(N)`**: sections over `W` are the `H`-equivariant locally constant
maps `W ×_X A → N`, with restriction by pullback of functions. -/
def descentPresheaf : (X.Etale)ᵒᵖ ⥤ ModuleCat.{max u v} Λ where
  obj W := ModuleCat.of Λ (G.equivariantMaps Λ N ρ W.unop)
  map {W W'} g := ModuleCat.ofHom
    { toFun f := ⟨LocallyConstant.comapₗ Λ (G.pullbackMap g.unop).base.hom f.1,
        G.comap_mem_equivariantMaps g.unop f.2⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  map_id W := by
    ext f z
    change f.1 ((G.pullbackMap (𝟙 W.unop)).base z) = f.1 z
    rw [G.pullbackMap_id]
    rfl
  map_comp {W W' W''} g g' := by
    ext f z
    change f.1 ((G.pullbackMap (g'.unop ≫ g.unop)).base z) =
      f.1 ((G.pullbackMap g.unop).base ((G.pullbackMap g'.unop).base z))
    rw [G.pullbackMap_comp, Scheme.Hom.comp_apply]

variable {Λ N ρ} in
/-- Restriction in the descent presheaf is precomposition with the induced map of fibre
products. -/
@[simp]
theorem descentPresheaf_map_apply {W W' : (X.Etale)ᵒᵖ} (g : W ⟶ W')
    (f : (G.descentPresheaf Λ N ρ).obj W) (z : G.fiberProd W'.unop) :
    (((G.descentPresheaf Λ N ρ).map g).hom f).1 z = f.1 ((G.pullbackMap g.unop).base z) :=
  rfl

end Descent

/-- Base change along the covering is the fibre product with it, on morphisms as well. -/
theorem smallEtaleBaseChange_map_left {W W' : X.Etale} (g : W' ⟶ W) :
    ((Stacks.EtaleCohomology.smallEtaleBaseChange (Y := X) G.cover.hom).map g).left =
      G.pullbackMap g := by
  apply pullback.hom_ext
  · exact (Stacks.EtaleCohomology.smallEtaleBaseChange_map_left_fst _ g).trans
      (G.pullbackMap_fst g).symm
  · exact (Stacks.EtaleCohomology.smallEtaleBaseChange_w _
      ((Stacks.EtaleCohomology.smallEtaleBaseChange (Y := X) G.cover.hom).map g)).trans
      (G.pullbackMap_snd g).symm

section Sheaf

variable (Λ : Type r) [Ring Λ] (N : Type (max (u + 1) v)) [AddCommGroup N] [Module Λ N]
  (ρ : H →* Module.End Λ N)

/-- The presheaf of sets of all locally constant maps `W ×_X A → N`. -/
abbrev allMapsTypePresheaf : (X.Etale)ᵒᵖ ⥤ Type (max (u + 1) v) where
  obj W := LocallyConstant (G.fiberProd W.unop) N
  map g := ↾ fun t ↦ LocallyConstant.comap (G.pullbackMap g.unop).base.hom t
  map_id W := by
    ext t z
    change t ((G.pullbackMap (𝟙 W.unop)).base z) = t z
    rw [G.pullbackMap_id]
    rfl
  map_comp g g' := by
    ext t z
    change t ((G.pullbackMap (g'.unop ≫ g.unop)).base z) =
      t ((G.pullbackMap g.unop).base ((G.pullbackMap g'.unop).base z))
    rw [G.pullbackMap_comp, Scheme.Hom.comp_apply]

/-- The presheaf of sets of all locally constant maps `W ×_X A → N` is the direct image along the
covering of the sheaf of locally constant maps on `A`, read on underlying sets. -/
def allMapsTypePresheafIso :
    ((Stacks.EtaleCohomology.smallEtaleBaseChange (Y := X) G.cover.hom).op ⋙
        smallEtaleLocallyConstantMapsAb.{u, max (u + 1) v} G.cover.left N) ⋙
      forget AddCommGrpCat ≅ G.allMapsTypePresheaf N :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro W W' g
    ext t z
    exact congrArg (fun k ↦ (show LocallyConstant (G.fiberProd W.unop) N from t) (k.base z))
      (G.smallEtaleBaseChange_map_left g.unop))

/-- The locally constant maps `W ×_X A → N` form a sheaf of sets. -/
theorem isSheaf_allMapsTypePresheaf :
    Presieve.IsSheaf (Scheme.smallEtaleTopology X) (G.allMapsTypePresheaf N) := by
  have : (Stacks.EtaleCohomology.smallEtaleBaseChange (Y := X) G.cover.hom).IsContinuous
      (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology G.cover.left) :=
    Stacks.EtaleCohomology.smallEtaleBaseChange_isContinuous _
  have hall₀ := Functor.op_comp_isSheaf_of_isSheaf
    (Stacks.EtaleCohomology.smallEtaleBaseChange (Y := X) G.cover.hom)
    (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology G.cover.left)
    (smallEtaleLocallyConstantMapsAb.{u, max (u + 1) v} G.cover.left N)
    (smallEtaleLocallyConstantMapsAb_isSheaf.{u, v} G.cover.left N)
  have hall₂ := Presheaf.isSheaf_comp_of_isSheaf (Scheme.smallEtaleTopology X) _
    (forget AddCommGrpCat) hall₀
  exact (isSheaf_iff_isSheaf_of_type _ _).1
    ((Presheaf.isSheaf_of_iso_iff (G.allMapsTypePresheafIso N)).1 hall₂)

/-- The presheaf of sets of equivariant locally constant maps. -/
abbrev descentTypePresheaf : (X.Etale)ᵒᵖ ⥤ Type (max (u + 1) v) where
  obj W := G.equivariantMaps Λ N ρ W.unop
  map g := ↾ fun f ↦ ⟨LocallyConstant.comapₗ Λ (G.pullbackMap g.unop).base.hom f.1,
    G.comap_mem_equivariantMaps g.unop f.2⟩
  map_id W := by
    ext f z
    change f.1 ((G.pullbackMap (𝟙 W.unop)).base z) = f.1 z
    rw [G.pullbackMap_id]
    rfl
  map_comp g g' := by
    ext f z
    change f.1 ((G.pullbackMap (g'.unop ≫ g.unop)).base z) =
      f.1 ((G.pullbackMap g.unop).base ((G.pullbackMap g'.unop).base z))
    rw [G.pullbackMap_comp, Scheme.Hom.comp_apply]

/-- The presheaf of sets of equivariant maps is the underlying presheaf of sets of the descent
presheaf. -/
def descentTypePresheafIso :
    (G.descentPresheaf Λ N ρ ⋙ forget₂ _ AddCommGrpCat) ⋙ forget AddCommGrpCat ≅
      G.descentTypePresheaf Λ N ρ :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)

/-- **The equivariant maps form a sheaf of sets.** Sections of the sheaf of all locally constant
maps glue, and the glued map is equivariant because its two translates by an element of `H`
glue the same family. -/
theorem isSheaf_descentTypePresheaf :
    Presieve.IsSheaf (Scheme.smallEtaleTopology X) (G.descentTypePresheaf Λ N ρ) := by
  intro W S hS
  have hP := G.isSheaf_allMapsTypePresheaf N S hS
  have hres : ∀ {V : X.Etale} (g : V ⟶ W) (t : LocallyConstant (G.fiberProd W) N)
      (z : G.fiberProd V),
        (show LocallyConstant (G.fiberProd V) N from (G.allMapsTypePresheaf N).map g.op t) z =
          t ((G.pullbackMap g).base z) := fun _ _ _ ↦ rfl
  intro x hx
  let y : Presieve.FamilyOfElements (G.allMapsTypePresheaf N) S :=
    fun V g hg ↦ ((x g hg).1 : LocallyConstant (G.fiberProd V) N)
  have hy : y.Compatible := by
    intro V₁ V₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ hcomm
    exact congrArg Subtype.val (hx g₁ g₂ hf₁ hf₂ hcomm)
  obtain ⟨t, ht, -⟩ := hP y hy
  have heq : t ∈ G.equivariantMaps Λ N ρ W := by
    intro h z
    let t₁ : LocallyConstant (G.fiberProd W) N :=
      LocallyConstant.comap (G.pullbackAct W h).base.hom t
    let t₂ : LocallyConstant (G.fiberProd W) N :=
      ⟨fun z ↦ ρ h (t z), t.isLocallyConstant.comp _⟩
    suffices h₁₂ : t₁ = t₂ by
      have h' := congrArg (fun f : LocallyConstant _ N ↦ f z) h₁₂
      exact h'
    refine hP.isSeparatedFor.ext fun V g hg ↦ LocallyConstant.ext fun y' ↦ ?_
    have hxg : (G.allMapsTypePresheaf N).map g.op t = (x g hg).1 := ht g hg
    rw [hres, hres]
    show t ((G.pullbackAct W h).base ((G.pullbackMap g).base y')) =
      ρ h (t ((G.pullbackMap g).base y'))
    rw [← Scheme.Hom.comp_apply, G.pullbackMap_pullbackAct, Scheme.Hom.comp_apply,
      ← hres g t, ← hres g t, hxg]
    exact (x g hg).2 h y'
  refine ⟨⟨t, heq⟩, fun V g hg ↦ Subtype.ext (ht g hg), fun y₁ hy₁ ↦ Subtype.ext ?_⟩
  exact (hP y hy).unique (fun V g hg ↦ congrArg Subtype.val (hy₁ g hg)) ht

/-- **The descent presheaf is a sheaf.** -/
theorem isSheaf_descentPresheaf :
    Presheaf.IsSheaf (Scheme.smallEtaleTopology X) (G.descentPresheaf Λ N ρ) := by
  refine Presheaf.isSheaf_of_isSheaf_comp (Scheme.smallEtaleTopology X) _
    (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat) ?_
  refine Presheaf.isSheaf_of_isSheaf_comp (Scheme.smallEtaleTopology X) _
    (forget AddCommGrpCat) ?_
  exact (Presheaf.isSheaf_of_iso_iff (G.descentTypePresheafIso Λ N ρ)).2
    ((isSheaf_iff_isSheaf_of_type _ _).2 (G.isSheaf_descentTypePresheaf Λ N ρ))

/-- **The descent sheaf `D(N)`.** -/
abbrev descentSheaf : Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{max (u + 1) v} Λ) :=
  ⟨G.descentPresheaf Λ N ρ, G.isSheaf_descentPresheaf Λ N ρ⟩

end Sheaf

/-! ### The restriction of the descent sheaf to the covering -/

section Restriction

variable (Λ : Type r) [Ring Λ] (N : Type v) [AddCommGroup N] [Module Λ N]
  (ρ : H →* Module.End Λ N)

variable {Λ N ρ} in
/-- On a sheet, an equivariant map is determined by its value on the graph. -/
theorem apply_eq_of_mem_sheet {T : Over G.cover}
    {f : LocallyConstant (G.fiberProd T.left) N} (hf : f ∈ G.equivariantMaps Λ N ρ T.left)
    {z : G.fiberProd T.left} {h : H} (hz : z ∈ G.sheet T h) :
    f z = ρ h (f ((G.graph T).base ((pullback.fst T.left.hom G.cover.hom).base z))) := by
  have e : (G.sheet T h).ι = (G.sheet T h).ι ≫ pullback.fst _ _ ≫ G.graph T ≫
      G.pullbackAct T.left h := by
    apply pullback.hom_ext
    · simp
    · calc (G.sheet T h).ι ≫ pullback.snd _ _
          = (G.sheet T h).ι ≫ (pullback.fst _ _ ≫ T.hom.left) ≫ G.act h :=
            (G.sheet_ι_comp T h).symm
        _ = _ := by simp
  have hz' := congrArg (fun k ↦ k.base ⟨z, hz⟩) e
  simp only [Scheme.Opens.ι_apply] at hz'
  rw [← hf h]
  exact congrArg f hz'

/-- The sheet of a point of the graph is the neutral element. -/
theorem graph_mem_sheet_one (T : Over G.cover) (y : T.left.left) :
    (G.graph T).base y ∈ G.sheet T 1 :=
  Scheme.Hom.mem_agreeLocus_of_comp_eq _ _ _ _ (G.graph T) (by simp [G.act_one]) y

/-- Translating a point by `h'` moves it from the sheet of `h` to the sheet of `h' * h`. -/
theorem pullbackAct_mem_sheet (T : Over G.cover) {z : G.fiberProd T.left} {h : H}
    (hz : z ∈ G.sheet T h) (h' : H) :
    (G.pullbackAct T.left h').base z ∈ G.sheet T (h' * h) := by
  refine Scheme.Hom.mem_agreeLocus_of_comp_eq _ _ _ _
    ((G.sheet T h).ι ≫ G.pullbackAct T.left h') ?_ ⟨z, hz⟩
  · simp only [Category.assoc]
    rw [pullbackAct_fst_assoc, pullbackAct_snd, G.act_mul]
    simpa only [Category.assoc] using congrArg (· ≫ G.act h') (G.sheet_ι_comp T h)

/-- The sheet containing a point. -/
noncomputable def sheetIndex (T : Over G.cover) (z : G.fiberProd T.left) : H :=
  (G.exists_mem_sheet T z).choose

/-- A point lies on the sheet of its index. -/
theorem mem_sheet_sheetIndex (T : Over G.cover) (z : G.fiberProd T.left) :
    z ∈ G.sheet T (G.sheetIndex T z) :=
  (G.exists_mem_sheet T z).choose_spec

/-- The index of a point on the sheet of `h` is `h`. -/
theorem sheetIndex_eq {T : Over G.cover} {z : G.fiberProd T.left} {h : H}
    (hz : z ∈ G.sheet T h) : G.sheetIndex T z = h :=
  G.eq_of_mem_sheet T (G.mem_sheet_sheetIndex T z) hz

/-- The sheet index is a locally constant function on `T ×_X A`. -/
theorem isLocallyConstant_sheetIndex (T : Over G.cover) :
    IsLocallyConstant (G.sheetIndex T) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro z
  exact ⟨G.sheet T (G.sheetIndex T z), (G.sheet T _).2, G.mem_sheet_sheetIndex T z,
    fun z' hz' ↦ G.sheetIndex_eq hz'⟩

/-- The restriction of an equivariant map to the graph. -/
def restrictGraph (T : Over G.cover) :
    G.equivariantMaps Λ N ρ T.left →ₗ[Λ] LocallyConstant T.left.left N where
  toFun f := LocallyConstant.comap (G.graph T).base.hom f.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The equivariant map with a prescribed restriction to the graph. -/
def extendFromGraph (T : Over G.cover) (c : LocallyConstant T.left.left N) :
    G.equivariantMaps Λ N ρ T.left :=
  ⟨⟨fun z ↦ ρ (G.sheetIndex T z) (c ((pullback.fst T.left.hom G.cover.hom).base z)), by
      have h₁ := G.isLocallyConstant_sheetIndex T
      have h₂ : IsLocallyConstant (fun z : G.fiberProd T.left ↦
          c ((pullback.fst T.left.hom G.cover.hom).base z)) :=
        c.isLocallyConstant.comp_continuous
          (pullback.fst T.left.hom G.cover.hom).base.hom.continuous
      exact h₁.prodMk h₂ |>.comp (fun p : H × N ↦ ρ p.1 p.2)⟩, by
    intro h z
    change ρ (G.sheetIndex T ((G.pullbackAct T.left h).base z))
        (c ((pullback.fst T.left.hom G.cover.hom).base ((G.pullbackAct T.left h).base z))) =
      ρ h (ρ (G.sheetIndex T z) (c ((pullback.fst T.left.hom G.cover.hom).base z)))
    rw [G.sheetIndex_eq (G.pullbackAct_mem_sheet T (G.mem_sheet_sheetIndex T z) h),
      ← Scheme.Hom.comp_apply, pullbackAct_fst, map_mul, Module.End.mul_apply]⟩

/-- **Over the covering, an equivariant map is its restriction to the graph.** -/
theorem bijective_restrictGraph (T : Over G.cover) :
    Function.Bijective (G.restrictGraph Λ N ρ T) := by
  refine ⟨fun f₁ f₂ h ↦ Subtype.ext (LocallyConstant.ext fun z ↦ ?_), fun c ↦ ⟨G.extendFromGraph
    Λ N ρ T c, LocallyConstant.ext fun y ↦ ?_⟩⟩
  · have hz := G.mem_sheet_sheetIndex T z
    rw [G.apply_eq_of_mem_sheet f₁.2 hz, G.apply_eq_of_mem_sheet f₂.2 hz]
    exact congrArg (ρ _) (congrArg (fun k : LocallyConstant T.left.left N ↦
      k ((pullback.fst T.left.hom G.cover.hom).base z)) h)
  · show ρ (G.sheetIndex T ((G.graph T).base y))
      (c ((pullback.fst T.left.hom G.cover.hom).base ((G.graph T).base y))) = c y
    rw [G.sheetIndex_eq (G.graph_mem_sheet_one T y), map_one, ← Scheme.Hom.comp_apply,
      graph_fst]
    rfl

end Restriction

/-! ### The descent sheaf is constant on the covering -/

section Trivialization

variable (Λ : Type r) [Ring Λ] (N : Type (max (u + 1) v)) [AddCommGroup N] [Module Λ N]
  (ρ : H →* Module.End Λ N)

/-- **The restriction of the descent sheaf to the covering is the sheaf of locally constant
maps**: over an object `T` of the slice at `A`, an equivariant map on `T ×_X A` is its
restriction to the graph of `T ⟶ A`. -/
def restrictIso :
    ((Scheme.smallEtaleTopology X).overPullback (ModuleCat.{max (u + 1) v} Λ) G.cover).obj
        (G.descentSheaf Λ N ρ) ≅
      ((Scheme.smallEtaleTopology X).overPullback (ModuleCat.{max (u + 1) v} Λ) G.cover).obj
        (smallEtaleLocallyConstantMapsModuleSheaf.{u, v} Λ X (ModuleCat.of Λ N)) :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (NatIso.ofComponents
      (fun T ↦ (LinearEquiv.ofBijective (G.restrictGraph Λ N ρ T.unop)
        (G.bijective_restrictGraph Λ N ρ T.unop)).toModuleIso) (by
      intro T T' k
      ext f
      refine LocallyConstant.ext fun y ↦ ?_
      change f.1 ((G.pullbackMap k.unop.left).base ((G.graph T'.unop).base y)) =
        f.1 ((G.graph T.unop).base (k.unop.left.left.base y))
      exact congrArg (fun m ↦ f.1 (m.base y)) (G.graph_naturality k.unop).symm))

/-- **The descent sheaf `D(N)` is the constant sheaf `N̲` on the covering.** -/
def trivialization :
    (constantSheaf ((Scheme.smallEtaleTopology X).over G.cover)
        (ModuleCat.{max (u + 1) v} Λ)).obj (ModuleCat.of Λ N) ≅
      ((Scheme.smallEtaleTopology X).overPullback (ModuleCat.{max (u + 1) v} Λ) G.cover).obj
        (G.descentSheaf Λ N ρ) :=
  (Stacks.ConstantSheaf.overPullbackConstantSheafIso (Scheme.smallEtaleTopology X)
      (ModuleCat.{max (u + 1) v} Λ) G.cover).app (ModuleCat.of Λ N) ≪≫
    ((Scheme.smallEtaleTopology X).overPullback (ModuleCat.{max (u + 1) v} Λ) G.cover).mapIso
      (smallEtaleConstantSheafIsoLocallyConstantMapsModule.{u, v} Λ X (ModuleCat.of Λ N)) ≪≫
    (G.restrictIso Λ N ρ).symm

end Trivialization

/-! ### Morphisms of sheaves which are constant on the covering -/

section HomExt

/-- The covering is surjective. -/
instance surjective_cover_hom : Surjective G.cover.hom :=
  ⟨G.surjective⟩

/-- The fibre product `W ×_X A`, as an object of the small étale site over `W`. -/
def fiberObj (W : X.Etale) : X.Etale :=
  Scheme.Etale.mk (pullback.fst W.hom G.cover.hom ≫ W.hom)

/-- The first projection `W ×_X A ⟶ W`. -/
def fiberObjFst (W : X.Etale) : G.fiberObj W ⟶ W :=
  MorphismProperty.Over.homMk (pullback.fst W.hom G.cover.hom) rfl

/-- The second projection `W ×_X A ⟶ A`. -/
def fiberObjSnd (W : X.Etale) : G.fiberObj W ⟶ G.cover :=
  MorphismProperty.Over.homMk (pullback.snd W.hom G.cover.hom) pullback.condition.symm

/-- The first projection `W ×_X A ⟶ W` is an étale covering, the covering being surjective. -/
theorem ofArrows_fiberObjFst_mem (W : X.Etale) :
    Sieve.ofArrows (fun _ : PUnit.{u + 2} ↦ G.fiberObj W) (fun _ ↦ G.fiberObjFst W) ∈
      Scheme.smallEtaleTopology X W := by
  rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
  refine Set.eq_univ_of_forall fun w ↦ Set.mem_iUnion.2 ⟨PUnit.unit, ?_⟩
  show w ∈ Set.range (pullback.fst W.hom G.cover.hom).base
  rw [Scheme.Pullback.range_fst]
  exact G.surjective _

variable {Λ : Type r} [Ring Λ]

/-- **Two morphisms of sheaves which agree on the covering are equal.** -/
theorem hom_ext_of_overPullback_map_eq {F F' : Sheaf (Scheme.smallEtaleTopology X)
    (ModuleCat.{max (u + 1) r} Λ)} {φ ψ : F ⟶ F'}
    (h : ((Scheme.smallEtaleTopology X).overPullback _ G.cover).map φ =
      ((Scheme.smallEtaleTopology X).overPullback _ G.cover).map ψ) : φ = ψ := by
  apply Sheaf.hom_ext
  ext W : 2
  refine F'.property.hom_ext_ofArrows _ (G.ofArrows_fiberObjFst_mem W.unop) fun _ ↦ ?_
  rw [← φ.hom.naturality, ← ψ.hom.naturality]
  congr 1
  exact congrArg (fun k ↦ k.hom.app (op (Over.mk (G.fiberObjSnd W.unop)))) h

/-- **Morphisms out of a sheaf which is constant on the covering are determined by their value
over the covering itself.** The constant sheaf on the slice at the covering is left adjoint to
the sections over its terminal object. -/
theorem overPullback_hom_ext {M : ModuleCat.{max (u + 1) r} Λ}
    {F : Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{max (u + 1) r} Λ)}
    (e : (constantSheaf ((Scheme.smallEtaleTopology X).over G.cover)
        (ModuleCat.{max (u + 1) r} Λ)).obj M ≅
      ((Scheme.smallEtaleTopology X).overPullback _ G.cover).obj F)
    {G' : Sheaf ((Scheme.smallEtaleTopology X).over G.cover) (ModuleCat.{max (u + 1) r} Λ)}
    {χ₁ χ₂ : ((Scheme.smallEtaleTopology X).overPullback _ G.cover).obj F ⟶ G'}
    (h : χ₁.hom.app (op (Over.mk (𝟙 G.cover))) = χ₂.hom.app (op (Over.mk (𝟙 G.cover)))) :
    χ₁ = χ₂ := by
  rw [← cancel_epi e.hom]
  apply ((constantSheafAdj _ (ModuleCat.{max (u + 1) r} Λ)
      (Over.mkIdTerminal (X := G.cover))).homEquiv M G').injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  show _ ≫ (e.hom ≫ χ₁).hom.app _ = _ ≫ (e.hom ≫ χ₂).hom.app _
  show _ ≫ e.hom.hom.app _ ≫ χ₁.hom.app _ = _ ≫ e.hom.hom.app _ ≫ χ₂.hom.app _
  rw [h]

/-- **Morphisms out of a sheaf which is constant on the covering are determined by their value
over the covering.** -/
theorem hom_ext {M : ModuleCat.{max (u + 1) r} Λ}
    {F F' : Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{max (u + 1) r} Λ)}
    (e : (constantSheaf ((Scheme.smallEtaleTopology X).over G.cover)
        (ModuleCat.{max (u + 1) r} Λ)).obj M ≅
      ((Scheme.smallEtaleTopology X).overPullback _ G.cover).obj F)
    {φ ψ : F ⟶ F'} (h : φ.hom.app (op G.cover) = ψ.hom.app (op G.cover)) : φ = ψ :=
  G.hom_ext_of_overPullback_map_eq (G.overPullback_hom_ext e h)

end HomExt

/-! ### Equivariant maps of values on the covering extend to morphisms of sheaves -/

section Full

variable {Λ : Type r} [Ring Λ]

/-- The action of `h` followed by that of `h⁻¹` is the identity. -/
@[reassoc (attr := simp)]
theorem actHom_comp_actHom_inv (h : H) : G.actHom h ≫ G.actHom h⁻¹ = 𝟙 _ := by
  apply MorphismProperty.Over.Hom.ext
  show G.act h ≫ G.act h⁻¹ = 𝟙 _
  rw [← G.act_mul, inv_mul_cancel, G.act_one]

/-- The action of `h⁻¹` followed by that of `h` is the identity. -/
@[reassoc (attr := simp)]
theorem actHom_inv_comp_actHom (h : H) : G.actHom h⁻¹ ≫ G.actHom h = 𝟙 _ := by
  apply MorphismProperty.Over.Hom.ext
  show G.act h⁻¹ ≫ G.act h = 𝟙 _
  rw [← G.act_mul, mul_inv_cancel, G.act_one]

/-- Each element of the group acts by an automorphism of the covering. -/
instance isIso_actHom (h : H) : IsIso (G.actHom h) :=
  ⟨G.actHom h⁻¹, G.actHom_comp_actHom_inv h, G.actHom_inv_comp_actHom h⟩

/-- **The constants are the sections of a constant sheaf over the covering**, which is
irreducible. -/
theorem bijective_unit_constantSheafAdj (M : ModuleCat.{max (u + 1) r} Λ) :
    Function.Bijective (((constantSheafAdj ((Scheme.smallEtaleTopology X).over G.cover)
      (ModuleCat.{max (u + 1) r} Λ) (Over.mkIdTerminal (X := G.cover))).unit.app M)) := by
  rw [Stacks.ConstantSheaf.constantSheafAdj_unit_app]
  have hcomp := Stacks.ConstantSheaf.toSheafify_overPullbackConstantSheafIso
    (Scheme.smallEtaleTopology X) (ModuleCat.{max (u + 1) r} Λ) G.cover M
  have hbij := Scheme.bijective_toSheafify_const_app_of_irreducibleSpace Λ M G.cover
  have hiso : IsIso (((Stacks.ConstantSheaf.overPullbackConstantSheafIso
      (Scheme.smallEtaleTopology X) (ModuleCat.{max (u + 1) r} Λ) G.cover).hom.app M).hom.app
        (op (Over.mk (𝟙 G.cover)))) := inferInstance
  have hbij2 := (ConcreteCategory.isIso_iff_bijective _).1 hiso
  have hfun : ⇑(ConcreteCategory.hom ((toSheafify (Scheme.smallEtaleTopology X)
        ((Functor.const (X.Etale)ᵒᵖ).obj M)).app (op G.cover))) =
      (⇑(ConcreteCategory.hom (((Stacks.ConstantSheaf.overPullbackConstantSheafIso
          (Scheme.smallEtaleTopology X) (ModuleCat.{max (u + 1) r} Λ) G.cover).hom.app
            M).hom.app (op (Over.mk (𝟙 G.cover)))))) ∘
        (⇑(ConcreteCategory.hom ((toSheafify ((Scheme.smallEtaleTopology X).over G.cover)
          ((Functor.const (Over G.cover)ᵒᵖ).obj M)).app (op (Over.mk (𝟙 G.cover)))))) := by
    rw [← hcomp]
    rfl
  rw [hfun] at hbij
  exact (Function.Bijective.of_comp_iff' hbij2 _).1 hbij

variable {F F' : Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{max (u + 1) r} Λ)}
  {M : ModuleCat.{max (u + 1) r} Λ}
  (e : (constantSheaf ((Scheme.smallEtaleTopology X).over G.cover)
    (ModuleCat.{max (u + 1) r} Λ)).obj M ≅
      ((Scheme.smallEtaleTopology X).overPullback _ G.cover).obj F)
  (f : F.obj.obj (op G.cover) ⟶ F'.obj.obj (op G.cover))

/-- The morphism over the covering with a prescribed value over the covering itself. -/
def homOnCover :
    ((Scheme.smallEtaleTopology X).overPullback _ G.cover).obj F ⟶
      ((Scheme.smallEtaleTopology X).overPullback _ G.cover).obj F' :=
  e.inv ≫ ((constantSheafAdj _ (ModuleCat.{max (u + 1) r} Λ)
    (Over.mkIdTerminal (X := G.cover))).homEquiv M
      (((Scheme.smallEtaleTopology X).overPullback _ G.cover).obj F')).symm
      (((constantSheafAdj _ (ModuleCat.{max (u + 1) r} Λ)
        (Over.mkIdTerminal (X := G.cover))).unit.app M ≫
          e.hom.hom.app (op (Over.mk (𝟙 G.cover)))) ≫ f)

/-- The value of `homOnCover e f` over the covering itself is `f`. -/
theorem homOnCover_app_top :
    (G.homOnCover e f).hom.app (op (Over.mk (𝟙 G.cover))) = f := by
  set adj := constantSheafAdj ((Scheme.smallEtaleTopology X).over G.cover)
    (ModuleCat.{max (u + 1) r} Λ) (Over.mkIdTerminal (X := G.cover))
  set χ₀ := (adj.homEquiv M (((Scheme.smallEtaleTopology X).overPullback _ G.cover).obj F')).symm
    ((adj.unit.app M ≫ e.hom.hom.app (op (Over.mk (𝟙 G.cover)))) ≫ f)
  have h₀ : adj.unit.app M ≫ χ₀.hom.app (op (Over.mk (𝟙 G.cover))) =
      (adj.unit.app M ≫ e.hom.hom.app (op (Over.mk (𝟙 G.cover)))) ≫ f := by
    have := (adj.homEquiv M (((Scheme.smallEtaleTopology X).overPullback _ G.cover).obj
      F')).apply_symm_apply ((adj.unit.app M ≫ e.hom.hom.app (op (Over.mk (𝟙 G.cover)))) ≫ f)
    rw [Adjunction.homEquiv_unit] at this
    exact this
  have hepi : Epi (adj.unit.app M) :=
    (ModuleCat.epi_iff_surjective _).2 (G.bijective_unit_constantSheafAdj M).2
  have h₀' : adj.unit.app M ≫ χ₀.hom.app (op (Over.mk (𝟙 G.cover))) =
      adj.unit.app M ≫ e.hom.hom.app (op (Over.mk (𝟙 G.cover))) ≫ f :=
    h₀.trans (Category.assoc _ _ _)
  have h₁ := (cancel_epi (adj.unit.app M)).1 h₀'
  show e.inv.hom.app (op (Over.mk (𝟙 G.cover))) ≫ χ₀.hom.app (op (Over.mk (𝟙 G.cover))) = f
  rw [h₁]
  have hinv : e.inv.hom.app (op (Over.mk (𝟙 G.cover))) ≫
      e.hom.hom.app (op (Over.mk (𝟙 G.cover))) = 𝟙 _ := by
    rw [← NatTrans.comp_app]
    show (e.inv ≫ e.hom).hom.app _ = _
    rw [Iso.inv_hom_id]
    rfl
  ext x
  exact congrArg f.hom (ConcreteCategory.congr_hom hinv x)

variable (hf : ∀ h : H, F.obj.map (G.actHom h).op ≫ f = f ≫ F'.obj.map (G.actHom h).op)

include hf in
/-- **The morphism over the covering is invariant under the action**: restricting it along an
automorphism of the covering does not change it, because its value over the covering is
equivariant. -/
theorem presheafHom_map_actHom_homOnCover (h : H) :
    (presheafHom F.obj F'.obj).map (G.actHom h).op (G.homOnCover e f).hom =
      (G.homOnCover e f).hom := by
  let χ := (G.homOnCover e f).hom
  let χ' : ((Scheme.smallEtaleTopology X).overPullback _ G.cover).obj F ⟶
      ((Scheme.smallEtaleTopology X).overPullback _ G.cover).obj F' :=
    ⟨(presheafHom F.obj F'.obj).map (G.actHom h).op χ⟩
  suffices hχ : χ' = G.homOnCover e f from congrArg (fun k ↦ k.hom) hχ
  refine G.overPullback_hom_ext e ?_
  show ((presheafHom F.obj F'.obj).map (G.actHom h).op χ).app (op (Over.mk (𝟙 G.cover))) = _
  refine (presheafHom_map_app (𝟙 _) (G.actHom h) (G.actHom h) (by simp) χ).trans ?_
  rw [G.homOnCover_app_top e f]
  let k : Over.mk (G.actHom h) ⟶ Over.mk (𝟙 G.cover) := Over.homMk (G.actHom h) (by simp)
  have hnat := χ.naturality k.op
  change F.obj.map (G.actHom h).op ≫ χ.app (op (Over.mk (G.actHom h))) =
    χ.app (op (Over.mk (𝟙 G.cover))) ≫ F'.obj.map (G.actHom h).op at hnat
  have hnat' : F.obj.map (G.actHom h).op ≫ χ.app (op (Over.mk (G.actHom h))) =
      F.obj.map (G.actHom h).op ≫ f := by
    refine hnat.trans ?_
    rw [show χ.app (op (Over.mk (𝟙 G.cover))) = f from G.homOnCover_app_top e f]
    exact (hf h).symm
  exact (cancel_epi (F.obj.map (G.actHom h).op)).1 hnat'

include hf in
/-- **The morphism over the covering does not depend on how an object is mapped to the
covering**: two morphisms to the covering agree, locally, after the action of an element of
the group, under which the morphism over the covering is invariant. -/
theorem presheafHom_map_homOnCover_eq {V : X.Etale} (a b : V ⟶ G.cover) :
    (presheafHom F.obj F'.obj).map a.op (G.homOnCover e f).hom =
      (presheafHom F.obj F'.obj).map b.op (G.homOnCover e f).hom := by
  let P := presheafHom F.obj F'.obj
  have hP : Presieve.IsSheaf (Scheme.smallEtaleTopology X) P :=
    (isSheaf_iff_isSheaf_of_type _ _).1 (Presheaf.IsSheaf.hom F.obj F'.obj F'.property)
  have hab : ∀ h : H, (a.left ≫ G.act h) ≫ G.cover.hom = b.left ≫ G.cover.hom := fun h ↦ by
    rw [Category.assoc, G.act_comp_hom', MorphismProperty.Over.w a, MorphismProperty.Over.w b]
  let O : H → V.left.Opens := fun h ↦ Scheme.Hom.agreeLocus G.cover.hom _ _ (hab h)
  let Vh : H → X.Etale := fun h ↦ Scheme.Etale.mk ((O h).ι ≫ V.hom)
  let ι : ∀ h, Vh h ⟶ V := fun h ↦ MorphismProperty.Over.homMk (O h).ι rfl
  have hcov : Sieve.ofArrows Vh ι ∈ Scheme.smallEtaleTopology X V := by
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    refine Set.eq_univ_of_forall fun v ↦ Set.mem_iUnion.2 ?_
    obtain ⟨h, hw, hv⟩ := G.exists_mem_agreeLocus a.left b.left (by
      rw [MorphismProperty.Over.w a, MorphismProperty.Over.w b]) v
    refine ⟨h, ?_⟩
    show v ∈ Set.range (O h).ι.base
    rw [Scheme.Opens.range_ι]
    exact hv
  have heq : ∀ h, ι h ≫ b = ι h ≫ a ≫ G.actHom h := fun h ↦ by
    apply MorphismProperty.Over.Hom.ext
    exact (Scheme.Hom.agreeLocus_ι_comp G.cover.hom _ _ (hab h)).symm
  refine (hP _ hcov).isSeparatedFor.ext fun Z g hg ↦ ?_
  obtain ⟨h, k, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hg
  let χ := (G.homOnCover e f).hom
  have e1 : ∀ c : V ⟶ G.cover,
      P.map (k ≫ ι h).op (P.map c.op χ) = P.map ((k ≫ ι h) ≫ c).op χ :=
    fun c ↦ (Functor.map_comp_apply P c.op (k ≫ ι h).op χ).symm
  have e2 : (k ≫ ι h) ≫ b = ((k ≫ ι h) ≫ a) ≫ G.actHom h := by
    rw [Category.assoc k, heq h]
    simp only [Category.assoc]
  show P.map (k ≫ ι h).op (P.map a.op χ) = P.map (k ≫ ι h).op (P.map b.op χ)
  rw [e1 a, e1 b]
  calc P.map ((k ≫ ι h) ≫ a).op χ
      = P.map ((k ≫ ι h) ≫ a).op (P.map (G.actHom h).op χ) := by
        rw [G.presheafHom_map_actHom_homOnCover e f hf h]
    _ = P.map ((G.actHom h).op ≫ ((k ≫ ι h) ≫ a).op) χ :=
        (Functor.map_comp_apply P (G.actHom h).op ((k ≫ ι h) ≫ a).op χ).symm
    _ = P.map ((k ≫ ι h) ≫ b).op χ := by rw [e2]; rfl

include e hf in
/-- **An equivariant map of values over the covering extends to a morphism of sheaves**, when the
source is constant on the covering. The morphism over the covering does not depend on how an
étale scheme is mapped to the covering, so its restrictions glue in the sheaf of morphisms. -/
theorem exists_hom_app_cover_eq : ∃ φ : F ⟶ F', φ.hom.app (op G.cover) = f := by
  let P := presheafHom F.obj F'.obj
  have hP : Presieve.IsSheaf (Scheme.smallEtaleTopology X) P :=
    (isSheaf_iff_isSheaf_of_type _ _).1 (Presheaf.IsSheaf.hom F.obj F'.obj F'.property)
  let χ := (G.homOnCover e f).hom
  have hχ : ∀ {V : X.Etale} (a b : V ⟶ G.cover), P.map a.op χ = P.map b.op χ :=
    fun a b ↦ G.presheafHom_map_homOnCover_eq e f hf a b
  let S : ∀ W : X.Etale, Sieve W := fun W ↦
    { arrows := fun V _ ↦ Nonempty (V ⟶ G.cover)
      downward_closed := fun {_ _ _} ha k ↦ ⟨k ≫ ha.some⟩ }
  have hS : ∀ W, S W ∈ Scheme.smallEtaleTopology X W := fun W ↦
    (Scheme.smallEtaleTopology X).superset_covering
      (fun V g hg ↦ by
        obtain ⟨_, k, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hg
        exact ⟨k ≫ G.fiberObjSnd W⟩) (G.ofArrows_fiberObjFst_mem W)
  let x : ∀ W : X.Etale, Presieve.FamilyOfElements P (S W).arrows :=
    fun _ _ _ hg ↦ P.map (Nonempty.some hg).op χ
  have hx : ∀ W, (x W).Compatible := by
    intro W V₁ V₂ Z g₁ g₂ f₁ f₂ h₁ h₂ _
    show P.map g₁.op (P.map (Nonempty.some h₁).op χ) =
      P.map g₂.op (P.map (Nonempty.some h₂).op χ)
    refine (Functor.map_comp_apply P (Nonempty.some h₁).op g₁.op χ).symm.trans
      (Eq.trans ?_ (Functor.map_comp_apply P (Nonempty.some h₂).op g₂.op χ))
    exact hχ (g₁ ≫ Nonempty.some h₁) (g₂ ≫ Nonempty.some h₂)
  let t : ∀ W : (X.Etale)ᵒᵖ, P.obj W := fun W ↦ (hP _ (hS W.unop)).amalgamate (x W.unop) (hx _)
  have ht : ∀ (W : X.Etale) {V : X.Etale} (g : V ⟶ W) (a : V ⟶ G.cover),
      P.map g.op (t (op W)) = P.map a.op χ := fun W V g a ↦
    ((hP _ (hS W)).valid_glue (hx W) g ⟨a⟩).trans (hχ _ a)
  have hsec : ∀ {W W' : (X.Etale)ᵒᵖ} (g : W ⟶ W'), P.map g (t W) = t W' := by
    intro W W' g
    refine (hP _ (hS W'.unop)).isSeparatedFor.ext fun V k hk ↦ ?_
    refine (Functor.map_comp_apply P g k.op (t W)).symm.trans ?_
    refine Eq.trans ?_ (ht W'.unop k (Nonempty.some hk)).symm
    exact ht W.unop (k ≫ g.unop) (Nonempty.some hk)
  refine ⟨⟨presheafHomSectionsEquiv F.obj F'.obj ⟨t, hsec⟩⟩, ?_⟩
  have htA : t (op G.cover) = χ :=
    (hP _ (hS G.cover)).isSeparatedFor.ext fun V k hk ↦ ht G.cover k k
  show (t (op G.cover)).app (op (Over.mk (𝟙 _))) = f
  rw [htA]
  exact G.homOnCover_app_top e f

end Full

end EtaleGaloisCovering

end AlgebraicGeometry

end
