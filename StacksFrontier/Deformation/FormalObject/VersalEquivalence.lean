module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Fibrewise
public import StacksFrontier.Deformation.FormalObject.Basic
public import StacksFrontier.Deformation.FormalObject.VersalLifting

/-!
# Versality is invariant under an equivalence over the base

Let `p : F ⥤ 𝒞_{Λ,k}` and `q : G ⥤ 𝒞_{Λ,k}` be categories cofibered in groupoids and let
`φ : F ⥤ G` be an equivalence of categories with `φ ⋙ q = p`. Applying `φ` levelwise sends a
formal object of `p` to a formal object of `q` with the same base
(`Deformation.formalObjectMapOfCompEq`), and this file shows that it sends versal formal objects
to versal formal objects.

The proof runs through the intrinsic lifting criterion of Stacks 06HS
(`Deformation.isVersal_iff_lifts_artinian`). Two facts about the levelwise functor `Φ` are used:
it is full, because `φ` is full and lies over the base; and every formal object of `q` is
isomorphic, by an isomorphism over the identity of its base, to the image of a formal object of
`p`, because `φ` is essentially surjective and `p` is cofibered in groupoids, so that every object
of `G` is isomorphic over the identity to the image of an object of `F`.

## Main results

* `Deformation.exists_iso_isHomLift_id_of_comp_eq`: an essentially surjective functor over the
  base out of a category cofibered in groupoids is essentially surjective by isomorphisms lying
  over identities.
* `Deformation.isVersal_formalObjectMapOfCompEq`: versality is preserved by an equivalence over
  the base.
* `Deformation.exists_isVersal_base_eq_of_comp_eq`: the same, as the existence of a versal formal
  object over the same base.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v w uF vF uG vG uC vC

namespace Deformation

section Fibrewise

variable {C : Type uC} [Category.{vC} C]
variable {F : Type uF} [Category.{vF} F] {G : Type uG} [Category.{vG} G]

/-- **Essential surjectivity over the identity.** If `φ : F ⥤ G` is essentially surjective and
lies over the base, `φ ⋙ q = p`, and `p` is cofibered in groupoids, then every object of `G` is
isomorphic to the image of an object of `F` by an isomorphism lying over an identity. -/
theorem exists_iso_isHomLift_id_of_comp_eq {p : F ⥤ C} {q : G ⥤ C} (φ : F ⥤ G)
    (hφ : φ ⋙ q = p) [φ.EssSurj] (hp : IsCofiberedInGroupoids p) (y : G) :
    ∃ (x : F) (e : φ.obj x ≅ y), q.IsHomLift (𝟙 (q.obj y)) e.hom := by
  subst hφ
  let x₀ := φ.objPreimage y
  let e₀ : φ.obj x₀ ≅ y := φ.objObjPreimageIso y
  let c : (φ ⋙ q).obj x₀ ≅ q.obj y := q.mapIso e₀
  obtain ⟨z, hz, β, hβ⟩ := Functor.IsFiberedInGroupoids.exists_iso_lift hp
    (z := Opposite.op x₀) c.symm.op
  let x := z.unop
  let b : x ≅ x₀ := β.unop
  have hx : (φ ⋙ q).obj x = q.obj y := by
    simpa using congrArg Opposite.unop hz
  have hb : (φ ⋙ q).map b.hom = eqToHom hx ≫ c.inv := by
    have h := IsHomLift.fac' (φ ⋙ q).op c.symm.op.hom β.hom
    simpa [b, Functor.op_map] using congrArg (fun f => f.unop) h
  let e : φ.obj x ≅ y := φ.mapIso b ≪≫ e₀
  refine ⟨x, e, IsHomLift.of_fac' q _ e.hom hx rfl ?_⟩
  change q.map (φ.map b.hom ≫ e₀.hom) = _
  rw [q.map_comp]
  change (φ ⋙ q).map b.hom ≫ q.map e₀.hom = _
  rw [hb]
  simp [c]

end Fibrewise

section Versal

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {F : Type uF} [Category.{vF} F] {G : Type uG} [Category.{vG} G]
variable {q : G ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}

/-- A morphism `(φ ⋙ q).IsHomLift f g` is the same as `q.IsHomLift f (φ.map g)`. -/
private theorem isHomLift_comp_of_map (φ : F ⥤ G) {R S : ArtinianLocalAlgCat.{u, v, w} Λ k}
    {a b : F} {f : R ⟶ S} {g : a ⟶ b} (h : q.IsHomLift f (φ.map g)) :
    (φ ⋙ q).IsHomLift f g :=
  IsHomLift.of_fac (φ ⋙ q) f g (IsHomLift.domain_eq q f (φ.map g))
    (IsHomLift.codomain_eq q f (φ.map g)) (IsHomLift.fac q f (φ.map g))

/-- A morphism `q.IsHomLift f (φ.map g)` is the same as `(φ ⋙ q).IsHomLift f g`. -/
private theorem isHomLift_map_of_comp (φ : F ⥤ G) {R S : ArtinianLocalAlgCat.{u, v, w} Λ k}
    {a b : F} {f : R ⟶ S} {g : a ⟶ b} (h : (φ ⋙ q).IsHomLift f g) :
    q.IsHomLift f (φ.map g) :=
  IsHomLift.of_fac q f (φ.map g) (IsHomLift.domain_eq (φ ⋙ q) f g)
    (IsHomLift.codomain_eq (φ ⋙ q) f g) (IsHomLift.fac (φ ⋙ q) f g)

/-- The levelwise image of a formal object under `φ`, for `p = φ ⋙ q`. This is
`Deformation.formalObjectMapOfCompEq φ rfl`, written out so that its base and levels are
definitionally those of the input. -/
@[reducible] private def levelwise (φ : F ⥤ G) :
    FormalObject (φ ⋙ q) ⥤ FormalObject q where
  obj X :=
    { base := X.base
      level := fun n ↦ φ.obj (X.level n)
      level_eq := X.level_eq
      transition := fun n ↦ φ.map (X.transition n)
      transition_lift := fun n ↦ isHomLift_map_of_comp φ (X.transition_lift n) }
  map {X Y} f :=
    { base := f.base
      app := fun n ↦ φ.map (f.app n)
      app_lift := fun n ↦ isHomLift_map_of_comp φ (f.app_lift n)
      naturality := fun n ↦ by rw [← Functor.map_comp, f.naturality, Functor.map_comp] }
  map_id X := FormalObject.Hom.ext rfl fun n ↦ φ.map_id (X.level n)
  map_comp f g := FormalObject.Hom.ext rfl fun n ↦ φ.map_comp (f.app n) (g.app n)

/-- **The levelwise functor is full.** A morphism between levelwise images is the image of the
morphism with the same base whose level maps are the preimages under `φ`. -/
private theorem levelwise_map_surjective (φ : F ⥤ G) [φ.Full] [φ.Faithful]
    {X Y : FormalObject (φ ⋙ q)} (m : (levelwise φ).obj X ⟶ (levelwise φ).obj Y) :
    ∃ g : X ⟶ Y, (levelwise φ).map g = m := by
  let g : FormalObject.Hom X Y :=
    { base := m.base
      app := fun n => φ.preimage (m.app n)
      app_lift := fun n => isHomLift_comp_of_map φ (by simpa using m.app_lift n)
      naturality := fun n => by
        apply φ.map_injective
        simpa only [Functor.map_comp, Functor.map_preimage] using m.naturality n }
  exact ⟨g, FormalObject.Hom.ext rfl fun n ↦ φ.map_preimage (m.app n)⟩

/-- A hom-lift of an identity is a hom-lift of the identity of any equal object. -/
private theorem isHomLift_id_of_eq {R R' : ArtinianLocalAlgCat.{u, v, w} Λ k} (h : R = R')
    {a b : G} {f : a ⟶ b} (hf : q.IsHomLift (𝟙 R) f) : q.IsHomLift (𝟙 R') f := by
  subst h
  exact hf

/-- Levelwise preimages over the identity of the levels of a formal object of `q`, chosen by
`exists_iso_isHomLift_id_of_comp_eq`. -/
private def levelPreimage (φ : F ⥤ G) [φ.EssSurj] (hp : IsCofiberedInGroupoids (φ ⋙ q))
    (X : FormalObject q) (n : ℕ) : F :=
  (exists_iso_isHomLift_id_of_comp_eq (q := q) φ rfl hp (X.level n)).choose

/-- The chosen isomorphism from the image of a levelwise preimage. -/
private def levelPreimageIso (φ : F ⥤ G) [φ.EssSurj] (hp : IsCofiberedInGroupoids (φ ⋙ q))
    (X : FormalObject q) (n : ℕ) : φ.obj (levelPreimage φ hp X n) ≅ X.level n :=
  (exists_iso_isHomLift_id_of_comp_eq (q := q) φ rfl hp (X.level n)).choose_spec.choose

private theorem levelPreimageIso_lift (φ : F ⥤ G) [φ.EssSurj]
    (hp : IsCofiberedInGroupoids (φ ⋙ q)) (X : FormalObject q) (n : ℕ) :
    q.IsHomLift (𝟙 ((AdicTruncation.functor n).obj X.base))
      (levelPreimageIso φ hp X n).hom :=
  isHomLift_id_of_eq (X.level_eq n)
    (exists_iso_isHomLift_id_of_comp_eq (q := q) φ rfl hp (X.level n)).choose_spec.choose_spec

private theorem levelPreimageIso_inv_lift (φ : F ⥤ G) [φ.EssSurj]
    (hp : IsCofiberedInGroupoids (φ ⋙ q)) (X : FormalObject q) (n : ℕ) :
    q.IsHomLift (𝟙 ((AdicTruncation.functor n).obj X.base))
      (levelPreimageIso φ hp X n).inv := by
  have := levelPreimageIso_lift φ hp X n
  exact IsHomLift.lift_id_inv q _ (levelPreimageIso φ hp X n)

/-- **A preimage of a formal object of `q`.** Its levels are the chosen levelwise preimages and
its transitions are the preimages under `φ` of the conjugated transitions. -/
@[reducible] private def formalPreimage (φ : F ⥤ G) [φ.IsEquivalence]
    (hp : IsCofiberedInGroupoids (φ ⋙ q)) (X : FormalObject q) : FormalObject (φ ⋙ q) where
  base := X.base
  level := levelPreimage φ hp X
  level_eq n := by
    have := levelPreimageIso_lift φ hp X n
    exact IsHomLift.domain_eq q (𝟙 ((AdicTruncation.functor n).obj X.base))
      (levelPreimageIso φ hp X n).hom
  transition n := φ.preimage ((levelPreimageIso φ hp X (n + 1)).hom ≫ X.transition n ≫
    (levelPreimageIso φ hp X n).inv)
  transition_lift n := by
    apply isHomLift_comp_of_map φ
    rw [Functor.map_preimage]
    have h1 := levelPreimageIso_lift φ hp X (n + 1)
    have h2 := levelPreimageIso_inv_lift φ hp X n
    have h3 := X.transition_lift n
    simpa using IsHomLift.comp q (𝟙 _) _ (levelPreimageIso φ hp X (n + 1)).hom
      (X.transition n ≫ (levelPreimageIso φ hp X n).inv)

/-- The comparison morphism from the image of the preimage, over the identity of the base. -/
private def formalPreimageHom (φ : F ⥤ G) [φ.IsEquivalence]
    (hp : IsCofiberedInGroupoids (φ ⋙ q)) (X : FormalObject q) :
    (levelwise φ).obj (formalPreimage φ hp X) ⟶ X where
  base := 𝟙 X.base
  app n := (levelPreimageIso φ hp X n).hom
  app_lift n := by
    rw [CategoryTheory.Functor.map_id]
    exact levelPreimageIso_lift φ hp X n
  naturality n := by
    change φ.map (φ.preimage _) ≫ _ = _
    rw [Functor.map_preimage]
    simp

/-- The comparison morphism to the image of the preimage, over the identity of the base. -/
private def formalPreimageInv (φ : F ⥤ G) [φ.IsEquivalence]
    (hp : IsCofiberedInGroupoids (φ ⋙ q)) (X : FormalObject q) :
    X ⟶ (levelwise φ).obj (formalPreimage φ hp X) where
  base := 𝟙 X.base
  app n := (levelPreimageIso φ hp X n).inv
  app_lift n := by
    rw [CategoryTheory.Functor.map_id]
    exact levelPreimageIso_inv_lift φ hp X n
  naturality n := by
    change _ = _ ≫ φ.map (φ.preimage _)
    rw [Functor.map_preimage]
    simp

/-- **Every formal object of `q` is a levelwise image up to isomorphism over the identity.** -/
private def formalPreimageIso (φ : F ⥤ G) [φ.IsEquivalence]
    (hp : IsCofiberedInGroupoids (φ ⋙ q)) (X : FormalObject q) :
    (levelwise φ).obj (formalPreimage φ hp X) ≅ X where
  hom := formalPreimageHom φ hp X
  inv := formalPreimageInv φ hp X
  hom_inv_id := FormalObject.Hom.ext (Category.comp_id (𝟙 X.base))
    fun n ↦ (levelPreimageIso φ hp X n).hom_inv_id
  inv_hom_id := FormalObject.Hom.ext (Category.comp_id (𝟙 X.base))
    fun n ↦ (levelPreimageIso φ hp X n).inv_hom_id

/-- Versality, for `p = φ ⋙ q`, is preserved by the levelwise functor of an equivalence. -/
private theorem isVersal_levelwise (φ : F ⥤ G) [φ.IsEquivalence]
    (hp : IsCofiberedInGroupoids (φ ⋙ q)) (hq : IsCofiberedInGroupoids q)
    (ξ : FormalObject (φ ⋙ q)) (hξ : IsVersal hp ξ) :
    IsVersal hq ((levelwise φ).obj ξ) := by
  rw [isVersal_iff_lifts_artinian] at hξ ⊢
  intro B A f hf y' x' g' hg' a'
  let y := formalPreimage φ hp y'
  let x := formalPreimage φ hp x'
  let iy := formalPreimageIso φ hp y'
  let ix := formalPreimageIso φ hp x'
  obtain ⟨g, hg⟩ := levelwise_map_surjective φ (iy.hom ≫ g' ≫ ix.inv)
  obtain ⟨a, ha⟩ := levelwise_map_surjective φ (a' ≫ ix.inv)
  have hgbase : g.base = g'.base := by
    have h := congrArg FormalObject.Hom.base hg
    change g.base = 𝟙 _ ≫ g'.base ≫ 𝟙 _ at h
    rw [h]
    simp
  have hglift : (FormalObject.projection (p := φ ⋙ q)).IsHomLift
      (artinianToComplete.map f) g := by
    refine IsHomLift.of_fac' _ _ g
      (IsHomLift.domain_eq (FormalObject.projection (p := q)) (artinianToComplete.map f) g')
      (IsHomLift.codomain_eq (FormalObject.projection (p := q)) (artinianToComplete.map f) g') ?_
    have hfac := IsHomLift.fac' (FormalObject.projection (p := q))
      (artinianToComplete.map f) g'
    simp only [FormalObject.projection_map] at hfac ⊢
    rw [hgbase, hfac]
  obtain ⟨b, hb⟩ := hξ f hf g hglift a
  refine ⟨(levelwise φ).map b ≫ iy.hom, ?_⟩
  calc
    ((levelwise φ).map b ≫ iy.hom) ≫ g' =
        (levelwise φ).map b ≫ (iy.hom ≫ g' ≫ ix.inv) ≫ ix.hom := by
      simp
    _ = (levelwise φ).map (b ≫ g) ≫ ix.hom := by
      rw [← hg, Functor.map_comp, Category.assoc]
    _ = a' := by
      rw [hb, ha]
      simp

/-- **Versality is invariant under an equivalence over the base.** Let `p` and `q` be categories
cofibered in groupoids over `𝒞_{Λ,k}` and let `φ` be an equivalence with `φ ⋙ q = p`. Then the
levelwise image under `φ` of a versal formal object of `p` is a versal formal object of `q`. -/
theorem isVersal_formalObjectMapOfCompEq {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (φ : F ⥤ G) (hφ : φ ⋙ q = p) [φ.IsEquivalence]
    (hp : IsCofiberedInGroupoids p) (hq : IsCofiberedInGroupoids q)
    (ξ : FormalObject p) (hξ : IsVersal hp ξ) :
    IsVersal hq ((formalObjectMapOfCompEq φ hφ).obj ξ) := by
  subst hφ
  exact isVersal_levelwise φ hp hq ξ hξ

/-- **A versal formal object transported along an equivalence over the base.** For `p` and `q`
cofibered in groupoids over `𝒞_{Λ,k}` and an equivalence `φ` with `φ ⋙ q = p`, a versal formal
object of `p` over `R` gives a versal formal object of `q` over the same `R`. -/
theorem exists_isVersal_base_eq_of_comp_eq {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (φ : F ⥤ G) (hφ : φ ⋙ q = p) [φ.IsEquivalence]
    (hp : IsCofiberedInGroupoids p) (hq : IsCofiberedInGroupoids q)
    (ξ : FormalObject p) (hξ : IsVersal hp ξ) :
    ∃ η : FormalObject q, η.base = ξ.base ∧ IsVersal hq η := by
  subst hφ
  exact ⟨(levelwise φ).obj ξ, rfl, isVersal_levelwise φ hp hq ξ hξ⟩

end Versal

end Deformation

end
