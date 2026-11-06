module

public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackTwoFibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartCovers
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.SheafConditionAffine
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FromLocalAtSource
public import StacksFrontier.CategoryTheory.Sites.Stack.SquareCocone
public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge

/-!
# Morphisms out of an algebraic space into a stack descend along étale coverings

Let `T` be an algebraic space over `S`, let `{e k : T k ⟶ T}` be an étale covering of algebraic
spaces, and let `𝒴` be an algebraic stack over `S`. Read `T` and the `T k` as algebraic stacks
through `AlgebraicGeometry.Stack.algebraicSpaceStackFunctor`. This file proves that
2-morphisms between two 1-morphisms `T ⟶ 𝒴` are determined by their restrictions to the `T k`.

## Main results

* `AlgebraicGeometry.Space.exists_ofArrows_mem_topology_lift`: a point of `T` with values in an
  object `U` of the big fppf site lifts, along a covering family of `U`, to the members of an
  étale covering of `T`.
* `AlgebraicGeometry.Stack.hom₂_ext_of_isEtaleCovering`: two 2-morphisms between 1-morphisms out
  of `T` which agree after whiskering by every `e k` are equal.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory

universe u v w

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasPullback_presheaf_AlgebraicSpaceStackHomDescent
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- **A point lifts locally along an étale covering.** Let `{q i : Y i ⟶ Z}` be an étale covering
of algebraic spaces and let `z : U ⟶ Z` be a point of `Z` with values in an object `U` of the big
fppf site. There is a covering family `{h i : V i ⟶ U}` of `U`, indexed by the same type, along
which `z` lifts to the members: `z ∘ h i` factors through `q i`.

The family is the one of the charts of the fibre products `U ×_Z Y i`, whose composites to `U`
are étale and jointly surjective. -/
theorem exists_ofArrows_mem_topology_lift {I : Type v} {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {Yi : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {qi : ∀ i, Yi i ⟶ Z}
    (hcov : IsEtaleCovering B S hS Yi qi) (U : BigFppfOver B S hS) (z : yoneda.obj U ⟶ Z) :
    ∃ (V : I → BigFppfOver B S hS) (h : ∀ i, V i ⟶ U) (y : ∀ i, yoneda.obj (V i) ⟶ Yi i),
      Sieve.ofArrows V h ∈ BigFppfOver.topology B S hS U ∧
        ∀ i, y i ≫ qi i = yoneda.map (h i) ≫ z := by
  classical
  let Zs : AlgebraicSpaces B S hS := ⟨Z, hcov.target_isAlgebraicSpace⟩
  let Ts : AlgebraicSpaces B S hS := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS _⟩
  let Ys : I → AlgebraicSpaces B S hS := fun i => ⟨Yi i, hcov.source_isAlgebraicSpace i⟩
  have hpb : IsEtaleCovering B S hS (fun i => pullback (qi i) z)
      (fun i => pullback.snd (qi i) z) :=
    isEtaleCovering_pullback_snd B S hS Ys (fun i => (ObjectProperty.homMk (qi i) : Ys i ⟶ Zs))
      (ObjectProperty.homMk z : Ts ⟶ Zs) hcov
  choose W a hsurj het using fun i => (hpb.source_isAlgebraicSpace i).exists_atlas
  let h : ∀ i, W i ⟶ U := fun i => yoneda.preimage (a i ≫ pullback.snd (qi i) z)
  have hh : ∀ i, yoneda.map (h i) = a i ≫ pullback.snd (qi i) z := fun i =>
    Functor.map_preimage _ _
  have hEt : ∀ i, Etale ((BigFppfOver.toScheme B S hS).map (h i)) := by
    intro i
    have : IsEtale B S hS (yoneda.map (h i)) := by
      rw [hh]
      exact isEtale_comp B S hS (isEtale_of_presheaf_etale B S hS (het i)) (hpb.etale i)
    exact (presheaf_yoneda_map_etale_iff B S hS (h i)).1 (presheaf_etale_of_isEtale B S hS this)
  have hjs : ∀ x : (BigFppfOver.toScheme B S hS).obj U,
      ∃ i, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (h i)) :=
    scheme_family_jointly_surjective_of_points B S hS W U h (by
      refine Set.eq_univ_of_forall fun p => ?_
      have hp : p ∈ ⋃ i, Set.range (pointsMap B S hS (pullback (qi i) z)
          (pullback.snd (qi i) z)) := by
        rw [hpb.jointly_surjective]
        trivial
      obtain ⟨i, w, hw⟩ := Set.mem_iUnion.1 hp
      obtain ⟨v, rfl⟩ := isSurjective_of_presheafSurjective B S hS (a i) (hsurj i) w
      exact Set.mem_iUnion.2 ⟨i, v, by rwa [hh, pointsMap_comp_apply]⟩)
  refine ⟨W, h, fun i => a i ≫ pullback.fst (qi i) z,
    BigFppfOver.sieve_generate_ofArrows_mem_topology W h
      (Scheme.etalePrecoverage_le_fppfPrecoverage _
        (Scheme.ofArrows_mem_etalePrecoverage_iff.2 ⟨hjs, hEt⟩)), fun i => ?_⟩
  rw [hh, Category.assoc, Category.assoc, pullback.condition]

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **An algebraic stack is a stack in groupoids at every index universe.** The stack clause of
`AlgebraicGeometry.Stack.IsAlgebraicStack` contains the sieve-indexed condition of Stacks 026F,
which gives the family-indexed condition of Stacks 02ZI for covering families indexed by any
universe through `CategoryTheory.Functor.IsStack.isStackInGroupoids`. -/
theorem AlgebraicStacks.isStackInGroupoids (𝒴 : AlgebraicStacks.{u, w} B S hS) :
    𝒴.val.val.p.IsStackInGroupoids.{v} (BigFppfOver.topology B S hS) := by
  obtain ⟨h𝒴, ⟨hst, -⟩, -⟩ := 𝒴.property
  exact hst.isStackInGroupoids h𝒴

/-- **The morphism of the category of elements of `T` lying over a lift of a point.** If the point
`t` of `T` over `U`, restricted along `h : V ⟶ U`, factors as `y ≫ e`, then the object `(V, y)` of
the category of elements of `T'` is sent by the 1-morphism attached to `e` to an object with a
morphism to `(U, t)` lying over `h`. -/
def liftHom {T T' : AlgebraicSpaces B S hS} (e : T' ⟶ T) {U V : BigFppfOver B S hS}
    (h : V ⟶ U) (t : T.obj.obj (Opposite.op U)) (y : yoneda.obj V ⟶ T'.obj)
    (hy : y ≫ e.hom = yoneda.map h ≫ yonedaEquiv.symm t) :
    ((algebraicSpaceStackFunctor.{u, w} B S hS).map e).hom.hom.obj
        (⟨V, Discrete.mk (yonedaEquiv y)⟩ :
          ((algebraicSpaceStackFunctor.{u, w} B S hS).obj T').val.val.obj) ⟶
      (⟨U, Discrete.mk t⟩ :
        ((algebraicSpaceStackFunctor.{u, w} B S hS).obj T).val.val.obj) := by
  refine eqToHom (associatedMap_obj B S hS e.hom _) ≫ ⟨h, Discrete.eqToHom ?_⟩
  change e.hom.app _ (yonedaEquiv y) = T.obj.map h.op t
  rw [← yonedaEquiv_comp, hy, ← yonedaEquiv_naturality, Equiv.apply_symm_apply]

/-- `AlgebraicGeometry.Stack.liftHom` lies over `h`. -/
instance isHomLift_liftHom {T T' : AlgebraicSpaces B S hS} (e : T' ⟶ T) {U V : BigFppfOver B S hS}
    (h : V ⟶ U) (t : T.obj.obj (Opposite.op U)) (y : yoneda.obj V ⟶ T'.obj)
    (hy : y ≫ e.hom = yoneda.map h ≫ yonedaEquiv.symm t) :
    ((algebraicSpaceStackFunctor.{u, w} B S hS).obj T).val.val.p.IsHomLift h
      (liftHom.{u, w} e h t y hy) := by
  refine IsHomLift.of_fac' _ _ _ (BasedFunctor.w_obj _ _) rfl ?_
  refine (Functor.map_comp _ _ _).trans ?_
  refine (congrArg (· ≫ _) (eqToHom_map _ _)).trans ?_
  rfl

/-- Morphisms of an algebraic stack over the same morphism are equal if they agree after
composing with the members of a covering family, with the overlaps the fibre products. -/
private theorem hom_ext_of_cover_pullback {𝒴 : AlgebraicStacks.{u, w} B S hS}
    {U Z : BigFppfOver B S hS} {K : Type v} {V : K → BigFppfOver B S hS} (hV : ∀ k, V k ⟶ U)
    (hcov : Sieve.ofArrows V hV ∈ BigFppfOver.topology B S hS U) (m : U ⟶ Z)
    {x z : 𝒴.val.val.obj} (hx : 𝒴.val.val.p.obj x = U) {x₁ : K → 𝒴.val.val.obj}
    (r : ∀ k, x₁ k ⟶ x) [∀ k, 𝒴.val.val.p.IsHomLift (hV k) (r k)]
    (hz : 𝒴.val.val.p.obj z = Z) {ζ ζ' : x ⟶ z} [𝒴.val.val.p.IsHomLift m ζ]
    [𝒴.val.val.p.IsHomLift m ζ'] (h : ∀ k, r k ≫ ζ = r k ≫ ζ') : ζ = ζ' :=
  (AlgebraicStacks.isStackInGroupoids.{u, v, w} 𝒴).hom_ext_of_cover hV hcov
    (fun k l => pullback.fst (hV k) (hV l)) (fun k l => pullback.snd (hV k) (hV l))
    (fun _ _ => IsPullback.of_hasPullback _ _) m hx r hz h

/-- **Two 2-morphisms out of an algebraic space agree as soon as they agree on an étale
covering.** Let `{e k : T k ⟶ T}` be an étale covering of algebraic spaces and let `β, β'` be
2-morphisms between two 1-morphisms `F, G : T ⟶ 𝒴` into an algebraic stack. If `β` and `β'` agree
after whiskering by every `e k`, then `β = β'`.

At an object `(U, t)` of `T` the point `t` lifts along a covering family of `U` to the members of
the covering (`AlgebraicGeometry.Space.exists_ofArrows_mem_topology_lift`); by naturality the two
components at `(U, t)` agree after composing with the images under `F` of the resulting morphisms,
and these are determined by that, `𝒴` being a stack in groupoids. -/
theorem hom₂_ext_of_isEtaleCovering {𝒴 : AlgebraicStacks.{u, w} B S hS}
    {T : AlgebraicSpaces B S hS} {K : Type v} {T' : K → AlgebraicSpaces B S hS}
    (e : ∀ k, T' k ⟶ T)
    (he : Space.IsEtaleCovering B S hS (fun k => (T' k).obj) (fun k => (e k).hom))
    {F G : (algebraicSpaceStackFunctor.{u, w} B S hS).obj T ⟶ 𝒴} {β β' : F ⟶ G}
    (h : ∀ k, (algebraicSpaceStackFunctor.{u, w} B S hS).map (e k) ◁ β =
      (algebraicSpaceStackFunctor.{u, w} B S hS).map (e k) ◁ β') : β = β' := by
  apply InducedBicategory.hom₂_ext
  apply InducedBicategory.hom₂_ext
  apply BasedNatTrans.ext
  ext ⟨U, ⟨t⟩⟩
  obtain ⟨V, hV, y, hcov, hy⟩ := Space.exists_ofArrows_mem_topology_lift he U (yonedaEquiv.symm t)
  have hr : ∀ k, 𝒴.val.val.p.IsHomLift (hV k)
      (F.hom.hom.map (liftHom.{u, w} (e k) (hV k) t (y k) (hy k))) := fun k =>
    have := isHomLift_liftHom.{u, w} (e k) (hV k) t (y k) (hy k)
    BasedFunctor.preserves_isHomLift F.hom.hom (hV k) _
  let o : ((algebraicSpaceStackFunctor.{u, w} B S hS).obj T).val.val.obj := ⟨U, ⟨t⟩⟩
  have hβ : 𝒴.val.val.p.IsHomLift (𝟙 U) (β.hom.hom.app o) := β.hom.hom.isHomLift' o
  have hβ' : 𝒴.val.val.p.IsHomLift (𝟙 U) (β'.hom.hom.app o) := β'.hom.hom.isHomLift' o
  refine hom_ext_of_cover_pullback hV hcov (𝟙 U) (BasedFunctor.w_obj F.hom.hom _)
    (fun k => F.hom.hom.map (liftHom.{u, w} (e k) (hV k) t (y k) (hy k)))
    (BasedFunctor.w_obj G.hom.hom _) fun k => ?_
  have n := β.hom.hom.naturality (liftHom.{u, w} (e k) (hV k) t (y k) (hy k))
  have n' := β'.hom.hom.naturality (liftHom.{u, w} (e k) (hV k) t (y k) (hy k))
  have hk := congrArg (fun γ => γ.hom.hom.app
    (⟨V k, Discrete.mk (yonedaEquiv (y k))⟩ :
      ((algebraicSpaceStackFunctor.{u, w} B S hS).obj (T' k)).val.val.obj)) (h k)
  exact n.trans ((congrArg (· ≫ G.hom.hom.map _) hk).trans n'.symm)

/-! ### Gluing 2-morphisms -/

/-- A component flanked by the images of an identity under two functors is unchanged. Stated for
plain functors so that it applies by unification where rewriting fails. -/
theorem map_id_comp_comp_map_id {C D : Type*} [Category C] [Category D] (F G : C ⥤ D) (X : C)
    (φ : F.obj X ⟶ G.obj X) : F.map (𝟙 X) ≫ φ ≫ G.map (𝟙 X) = φ := by
  simp

section Glue

/-- **Naturality of a transported component.** If a component `φ₂` at `Y₂` is natural along `μ`
with respect to `φ₁` at `Y₁`, then its transport to `X₂` along `j₂, j₂'` is natural along `κ` with
respect to the transport of `φ₁` to `X₁`, as soon as `κ` corresponds to `μ` under the
transports. Stated for plain functors so that it applies by unification. -/
theorem transport_naturality {C D : Type*} [Category C] [Category D] (F G : C ⥤ D)
    {X₁ X₂ Y₁ Y₂ : C} (κ : X₁ ⟶ X₂) (μ : Y₁ ⟶ Y₂) (j₁ : X₁ ⟶ Y₁) (j₂ : X₂ ⟶ Y₂)
    (j₁' : Y₁ ⟶ X₁) (j₂' : Y₂ ⟶ X₂) (φ₁ : F.obj Y₁ ⟶ G.obj Y₁) (φ₂ : F.obj Y₂ ⟶ G.obj Y₂)
    (h₁ : κ ≫ j₂ = j₁ ≫ μ) (h₂ : μ ≫ j₂' = j₁' ≫ κ) (hφ : F.map μ ≫ φ₂ = φ₁ ≫ G.map μ) :
    F.map κ ≫ (F.map j₂ ≫ φ₂ ≫ G.map j₂') = (F.map j₁ ≫ φ₁ ≫ G.map j₁') ≫ G.map κ := by
  rw [← Category.assoc, ← F.map_comp, h₁, F.map_comp, Category.assoc, ← Category.assoc (F.map μ),
    hφ, Category.assoc, ← G.map_comp, h₂, G.map_comp]
  simp only [Category.assoc]

/-- Bookkeeping for the overlap compatibility in the gluing of 2-morphisms, for plain functors. -/
theorem glue_compat_aux {C D : Type*} [Category C] [Category D] (F G : C ⥤ D)
    {X₁ X₂ Y Z : C} {x₂ : D} (c : x₂ ⟶ F.obj Y) (ρ₁ : Y ⟶ X₁) (ρ₂ : Y ⟶ X₂) (σ₁ : X₁ ⟶ Z)
    (σ₂ : X₂ ⟶ Z) (L₁ : F.obj X₁ ⟶ G.obj X₁) (L₂ : F.obj X₂ ⟶ G.obj X₂) (L : F.obj Y ⟶ G.obj Y)
    (N₁ : F.map ρ₁ ≫ L₁ = L ≫ G.map ρ₁) (N₂ : F.map ρ₂ ≫ L₂ = L ≫ G.map ρ₂)
    (hσ : ρ₁ ≫ σ₁ = ρ₂ ≫ σ₂) :
    (c ≫ F.map ρ₁) ≫ (L₁ ≫ G.map σ₁) = (c ≫ F.map ρ₂) ≫ (L₂ ≫ G.map σ₂) := by
  rw [Category.assoc, ← Category.assoc (F.map ρ₁), N₁, Category.assoc, ← G.map_comp, hσ,
    Category.assoc, ← Category.assoc (F.map ρ₂), N₂, Category.assoc, ← G.map_comp]

/-- Bookkeeping for the comparison of two fill-ins, for a plain functor. -/
theorem fill_compat_aux {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {Y X₁ X₂ Z : C} {x₂ : D} (c₁ c₂ : x₂ ⟶ F.obj Y) (ρ₁ : Y ⟶ X₁) (ρ₂ : Y ⟶ X₂) (σ₁ : X₁ ⟶ Z)
    (σ₂ : X₂ ⟶ Z) (r₁ : x₂ ⟶ F.obj X₁) (r₂ : x₂ ⟶ F.obj X₂) (h₁ : c₁ ≫ F.map ρ₁ = r₁)
    (h₂ : c₂ ≫ F.map ρ₂ = r₂) (h : r₁ ≫ F.map σ₁ = r₂ ≫ F.map σ₂) (hσ : ρ₁ ≫ σ₁ = ρ₂ ≫ σ₂) :
    c₁ ≫ F.map (ρ₁ ≫ σ₁) = c₂ ≫ F.map (ρ₁ ≫ σ₁) := by
  calc c₁ ≫ F.map (ρ₁ ≫ σ₁) = r₁ ≫ F.map σ₁ := by rw [F.map_comp, ← Category.assoc, h₁]
    _ = r₂ ≫ F.map σ₂ := h
    _ = c₂ ≫ F.map (ρ₁ ≫ σ₁) := by rw [hσ, F.map_comp, ← Category.assoc, h₂]

/-- Bookkeeping for the characterising property of the glued 2-morphism, for plain functors. -/
theorem key_aux {C D : Type*} [Category C] [Category D] (F G : C ⥤ D) {P W U V : C}
    (q : P ⟶ W) (κ : W ⟶ U) (ρ : P ⟶ V) (σ : V ⟶ U) (φ : F.obj U ⟶ G.obj U)
    (Lv : F.obj V ⟶ G.obj V) (Lw : F.obj W ⟶ G.obj W) (L : F.obj P ⟶ G.obj P)
    (hext : q ≫ κ = ρ ≫ σ) (hφ : F.map σ ≫ φ = Lv ≫ G.map σ)
    (Nv : F.map ρ ≫ Lv = L ≫ G.map ρ) (Nw : F.map q ≫ Lw = L ≫ G.map q) :
    F.map q ≫ (F.map κ ≫ φ) = F.map q ≫ (Lw ≫ G.map κ) := by
  rw [← Category.assoc, ← F.map_comp, hext, F.map_comp, Category.assoc, hφ,
    ← Category.assoc, Nv, Category.assoc, ← G.map_comp, ← hext, G.map_comp, ← Category.assoc,
    ← Nw, Category.assoc]

/-- Bookkeeping for the naturality of the glued 2-morphism, for plain functors. -/
theorem nat_aux {C D : Type*} [Category C] [Category D] (F G : C ⥤ D) {V U₁ U₂ : C}
    (q : V ⟶ U₁) (g : U₁ ⟶ U₂) (φ₁ : F.obj U₁ ⟶ G.obj U₁) (φ₂ : F.obj U₂ ⟶ G.obj U₂)
    (L : F.obj V ⟶ G.obj V) (h₂ : F.map (q ≫ g) ≫ φ₂ = L ≫ G.map (q ≫ g))
    (h₁ : F.map q ≫ φ₁ = L ≫ G.map q) :
    F.map q ≫ (F.map g ≫ φ₂) = F.map q ≫ (φ₁ ≫ G.map g) := by
  rw [← Category.assoc, ← F.map_comp, h₂, G.map_comp, ← Category.assoc, ← h₁, Category.assoc]

/-- Bookkeeping for the restriction of the glued 2-morphism, for plain functors. -/
theorem restrict_aux {C D : Type*} [Category C] [Category D] (F G : C ⥤ D) {U : C}
    (φ L : F.obj U ⟶ G.obj U) (h : F.map (𝟙 U) ≫ φ = L ≫ G.map (𝟙 U)) : φ = L := by
  simpa using h

variable {T T' : AlgebraicSpaces B S hS}

/-- The object `(U, t)` of the category of elements of the algebraic space `T`. -/
abbrev elt (T : AlgebraicSpaces B S hS) (U : BigFppfOver B S hS) (t : T.obj.obj (Opposite.op U)) :
    ((algebraicSpaceStackFunctor.{u, w} B S hS).obj T).val.val.obj :=
  ⟨U, ⟨t⟩⟩

/-- The morphism `(V, s) ⟶ (U, t)` of the category of elements of `T` lying over `h : V ⟶ U`,
for `s` the restriction of `t` along `h`. -/
def eltHom {U V : BigFppfOver B S hS} (h : V ⟶ U) {s : T.obj.obj (Opposite.op V)}
    {t : T.obj.obj (Opposite.op U)} (hst : s = T.obj.map h.op t) :
    elt.{u, w} T V s ⟶ elt.{u, w} T U t :=
  ⟨h, Discrete.eqToHom hst⟩

/-- **The category of elements of an algebraic space is fibred in sets**: a morphism is
determined by the morphism of the base it lies over. -/
theorem elt_hom_ext {X Y : ((algebraicSpaceStackFunctor.{u, w} B S hS).obj T).val.val.obj}
    {f g : X ⟶ Y} (h : f.base = g.base) : f = g :=
  Pseudofunctor.CoGrothendieck.Hom.ext _ _ h Discrete.hom_eq

/-- `AlgebraicGeometry.Stack.eltHom` lies over its base morphism. -/
instance isHomLift_eltHom {U V : BigFppfOver B S hS} (h : V ⟶ U) {s : T.obj.obj (Opposite.op V)}
    {t : T.obj.obj (Opposite.op U)} (hst : s = T.obj.map h.op t) :
    ((algebraicSpaceStackFunctor.{u, w} B S hS).obj T).val.val.p.IsHomLift h
      (eltHom.{u, w} h hst) :=
  IsHomLift.of_fac' _ _ _ rfl rfl ((Category.id_comp _).trans (Category.comp_id _)).symm

/-- Two equal points of `T` over `U` are related by restriction along the identity of `U`. -/
theorem eq_map_id {U : BigFppfOver B S hS} {s t : T.obj.obj (Opposite.op U)} (h : s = t) :
    s = T.obj.map (𝟙 U).op t := by
  rw [h, op_id, Functor.map_id_apply]

variable {𝒴 : AlgebraicStacks.{u, w} B S hS}
  {F G : (algebraicSpaceStackFunctor.{u, w} B S hS).obj T ⟶ 𝒴}

/-- **A 2-morphism on the members of a covering, read at a point of the target.** For
`e : T' ⟶ T`, a 2-morphism `β : e^* F ⟶ e^* G` and a point `a` of `T'` over `V` mapping to the
point `t` of `T`, the morphism `F(V, t) ⟶ G(V, t)` obtained from the component of `β` at `(V, a)`
by transport along the identification of `(V, e(a))` with `(V, t)`. -/
def localComp (e : T' ⟶ T)
    (β : (algebraicSpaceStackFunctor.{u, w} B S hS).map e ≫ F ⟶
      (algebraicSpaceStackFunctor.{u, w} B S hS).map e ≫ G)
    (V : BigFppfOver B S hS) (a : T'.obj.obj (Opposite.op V)) (t : T.obj.obj (Opposite.op V))
    (ha : e.hom.app _ a = t) :
    F.hom.hom.obj (elt.{u, w} T V t) ⟶ G.hom.hom.obj (elt.{u, w} T V t) :=
  F.hom.hom.map (eltHom.{u, w} (𝟙 V) (eq_map_id ha.symm)) ≫ β.hom.hom.app (elt.{u, w} T' V a) ≫
    G.hom.hom.map (eltHom.{u, w} (𝟙 V) (eq_map_id ha))

/-- At its own point, `AlgebraicGeometry.Stack.localComp` is the component of the 2-morphism. -/
theorem localComp_self (e : T' ⟶ T)
    (β : (algebraicSpaceStackFunctor.{u, w} B S hS).map e ≫ F ⟶
      (algebraicSpaceStackFunctor.{u, w} B S hS).map e ≫ G)
    (V : BigFppfOver B S hS) (a : T'.obj.obj (Opposite.op V)) :
    localComp e β V a _ rfl = β.hom.hom.app (elt.{u, w} T' V a) := by
  have h : eltHom.{u, w} (T := T) (𝟙 V) (eq_map_id (rfl : e.hom.app _ a = _)) = 𝟙 _ :=
    elt_hom_ext rfl
  rw [localComp, h]
  exact map_id_comp_comp_map_id _ _ _ _

/-- The point of the source of a morphism of the category of elements is the restriction of the
point of its target. -/
theorem point_eq_of_hom {V₁ V₂ : BigFppfOver B S hS} {t₁ : T.obj.obj (Opposite.op V₁)}
    {t₂ : T.obj.obj (Opposite.op V₂)} (κ : elt.{u, w} T V₁ t₁ ⟶ elt.{u, w} T V₂ t₂) :
    t₁ = T.obj.map κ.base.op t₂ :=
  Discrete.eq_of_hom κ.fiber

/-- A lift of the target point restricts to a lift of the source point. -/
theorem app_map_eq_of_hom (e : T' ⟶ T) {V₁ V₂ : BigFppfOver B S hS}
    {t₁ : T.obj.obj (Opposite.op V₁)} {t₂ : T.obj.obj (Opposite.op V₂)}
    (κ : elt.{u, w} T V₁ t₁ ⟶ elt.{u, w} T V₂ t₂) (a₂ : T'.obj.obj (Opposite.op V₂))
    (h₂ : e.hom.app _ a₂ = t₂) : e.hom.app _ (T'.obj.map κ.base.op a₂) = t₁ :=
  (NatTrans.naturality_apply e.hom κ.base.op a₂).trans
    ((congrArg (T.obj.map κ.base.op) h₂).trans (point_eq_of_hom κ).symm)

/-- **Naturality of `AlgebraicGeometry.Stack.localComp`.** Along a morphism
`κ : (V₁, t₁) ⟶ (V₂, t₂)` of the category of elements of `T`, the transported component at a lift
`a₂` of `t₂` and the one at its restriction, a lift of `t₁`, are related by `F(κ)` and `G(κ)`. -/
theorem localComp_naturality (e : T' ⟶ T)
    (β : (algebraicSpaceStackFunctor.{u, w} B S hS).map e ≫ F ⟶
      (algebraicSpaceStackFunctor.{u, w} B S hS).map e ≫ G)
    {V₁ V₂ : BigFppfOver B S hS} {t₁ : T.obj.obj (Opposite.op V₁)}
    {t₂ : T.obj.obj (Opposite.op V₂)} (κ : elt.{u, w} T V₁ t₁ ⟶ elt.{u, w} T V₂ t₂)
    (a₂ : T'.obj.obj (Opposite.op V₂)) (h₂ : e.hom.app _ a₂ = t₂) :
    F.hom.hom.map κ ≫ localComp e β V₂ a₂ t₂ h₂ =
      localComp e β V₁ (T'.obj.map κ.base.op a₂) t₁ (app_map_eq_of_hom e κ a₂ h₂) ≫
        G.hom.hom.map κ :=
  transport_naturality F.hom.hom.toFunctor G.hom.hom.toFunctor κ
    (((algebraicSpaceStackFunctor.{u, w} B S hS).map e).hom.hom.map
      (eltHom.{u, w} (T := T') κ.base rfl)) _ _ _ _ _ _ (elt_hom_ext (by simp; rfl))
    (elt_hom_ext (by simp; rfl))
    (β.hom.hom.naturality (eltHom.{u, w} (T := T') κ.base rfl))

/-- Every morphism of the category of elements of `T` lies over its base morphism. -/
theorem isHomLift_base {X Y : ((algebraicSpaceStackFunctor.{u, w} B S hS).obj T).val.val.obj}
    (κ : X ⟶ Y) : ((algebraicSpaceStackFunctor.{u, w} B S hS).obj T).val.val.p.IsHomLift κ.base κ :=
  IsHomLift.map _ κ

/-- A 1-morphism out of an algebraic space sends a morphism of the category of elements to a
morphism lying over its base morphism. -/
private theorem isHomLift_map_base (H : (algebraicSpaceStackFunctor.{u, w} B S hS).obj T ⟶ 𝒴)
    {X Y : ((algebraicSpaceStackFunctor.{u, w} B S hS).obj T).val.val.obj} (κ : X ⟶ Y) :
    𝒴.val.val.p.IsHomLift κ.base (H.hom.hom.map κ) :=
  have := isHomLift_base κ
  BasedFunctor.preserves_isHomLift H.hom.hom κ.base κ

/-- `AlgebraicGeometry.Stack.localComp` lies over an identity. -/
theorem isHomLift_localComp (e : T' ⟶ T)
    (β : (algebraicSpaceStackFunctor.{u, w} B S hS).map e ≫ F ⟶
      (algebraicSpaceStackFunctor.{u, w} B S hS).map e ≫ G)
    (V : BigFppfOver B S hS) (a : T'.obj.obj (Opposite.op V)) (t : T.obj.obj (Opposite.op V))
    (ha : e.hom.app _ a = t) : 𝒴.val.val.p.IsHomLift (𝟙 V) (localComp e β V a t ha) := by
  have h₁ := BasedFunctor.preserves_isHomLift F.hom.hom (𝟙 V)
    (eltHom.{u, w} (T := T) (𝟙 V) (eq_map_id ha.symm))
  have h₂ : 𝒴.val.val.p.IsHomLift (𝟙 V) (β.hom.hom.app (elt.{u, w} T' V a)) :=
    β.hom.hom.isHomLift' (elt.{u, w} T' V a)
  have h₃ := BasedFunctor.preserves_isHomLift G.hom.hom (𝟙 V)
    (eltHom.{u, w} (T := T) (𝟙 V) (eq_map_id ha))
  have h₂₃ : 𝒴.val.val.p.IsHomLift (𝟙 V) (β.hom.hom.app (elt.{u, w} T' V a) ≫
      G.hom.hom.map (eltHom.{u, w} (T := T) (𝟙 V) (eq_map_id ha))) :=
    @IsHomLift.comp_of_lift_id _ _ _ _ _ V _ _ _ _ _ h₂ h₃
  exact @IsHomLift.comp_of_lift_id _ _ _ _ _ V _ _ _ _ _ h₁ h₂₃

/-- **A point lifts locally along an étale covering, read on points.** The form of
`AlgebraicGeometry.Space.exists_ofArrows_mem_topology_lift` used for the category of elements. -/
theorem exists_cover_lift {K : Type v} {T' : K → AlgebraicSpaces B S hS} (e : ∀ k, T' k ⟶ T)
    (he : Space.IsEtaleCovering B S hS (fun k => (T' k).obj) (fun k => (e k).hom))
    (U : BigFppfOver B S hS) (t : T.obj.obj (Opposite.op U)) :
    ∃ (V : K → BigFppfOver B S hS) (hV : ∀ k, V k ⟶ U)
      (y : ∀ k, (T' k).obj.obj (Opposite.op (V k))),
      Sieve.ofArrows V hV ∈ BigFppfOver.topology B S hS U ∧
        ∀ k, (e k).hom.app _ (y k) = T.obj.map (hV k).op t := by
  obtain ⟨V, hV, y, hcov, hy⟩ := Space.exists_ofArrows_mem_topology_lift he U (yonedaEquiv.symm t)
  refine ⟨V, hV, fun k => yonedaEquiv (y k), hcov, fun k => ?_⟩
  rw [← yonedaEquiv_comp, hy, ← yonedaEquiv_naturality, Equiv.apply_symm_apply]

/-- **2-morphisms out of an algebraic space glue along an étale covering.** Let
`{e k : T k ⟶ T}` be an étale covering of algebraic spaces, let `F, G : T ⟶ 𝒴` be 1-morphisms into
an algebraic stack, and let `β k : e_k^* F ⟶ e_k^* G` be 2-morphisms which agree at every point
of `T` lifting to two members of the covering (`hβ`, read through
`AlgebraicGeometry.Stack.localComp`). Then there is a 2-morphism `γ : F ⟶ G` restricting to every
`β k`.

At an object `(U, t)` of `T` the point lifts along a covering family of `U` to the members of the
covering, and the component of `γ` is glued from the components of the `β k` there, `𝒴` being a
stack in groupoids (`CategoryTheory.Functor.IsStackInGroupoids.existsUnique_hom_of_cover`). The
glued component is characterised by its composites with all morphisms out of points that lift,
which gives naturality and the restriction to the `β k`. -/
theorem exists_hom₂_of_isEtaleCovering {K : Type v} {T' : K → AlgebraicSpaces B S hS}
    (e : ∀ k, T' k ⟶ T)
    (he : Space.IsEtaleCovering B S hS (fun k => (T' k).obj) (fun k => (e k).hom))
    (β : ∀ k, (algebraicSpaceStackFunctor.{u, w} B S hS).map (e k) ≫ F ⟶
      (algebraicSpaceStackFunctor.{u, w} B S hS).map (e k) ≫ G)
    (hβ : ∀ k l (V : BigFppfOver B S hS) (a : (T' k).obj.obj (Opposite.op V))
      (b : (T' l).obj.obj (Opposite.op V)) (hab : (e k).hom.app _ a = (e l).hom.app _ b),
      localComp (e k) (β k) V a _ hab = localComp (e l) (β l) V b _ rfl) :
    ∃ γ : F ⟶ G, ∀ k, (algebraicSpaceStackFunctor.{u, w} B S hS).map (e k) ◁ γ = β k := by
  classical
  have hp : 𝒴.val.val.p.IsStackInGroupoids.{v} (BigFppfOver.topology B S hS) :=
    AlgebraicStacks.isStackInGroupoids 𝒴
  have hg := hp.isFiberedInGroupoids
  have hβ' : ∀ k l (V : BigFppfOver B S hS) (a : (T' k).obj.obj (Opposite.op V))
      (b : (T' l).obj.obj (Opposite.op V)) (t : T.obj.obj (Opposite.op V))
      (ha : (e k).hom.app _ a = t) (hb : (e l).hom.app _ b = t),
      localComp (e k) (β k) V a t ha = localComp (e l) (β l) V b t hb := by
    intro k l V a b t ha hb
    subst hb
    exact hβ k l V a b ha
  -- the glued component at `(U, t)`, with its characterising property
  have key : ∀ (U : BigFppfOver B S hS) (t : T.obj.obj (Opposite.op U)),
      ∃ φ : F.hom.hom.obj (elt.{u, w} T U t) ⟶ G.hom.hom.obj (elt.{u, w} T U t),
        𝒴.val.val.p.IsHomLift (𝟙 U) φ ∧
        ∀ (W : BigFppfOver B S hS) (k : K) (a : (T' k).obj.obj (Opposite.op W))
          (s : T.obj.obj (Opposite.op W)) (ha : (e k).hom.app _ a = s)
          (κ : elt.{u, w} T W s ⟶ elt.{u, w} T U t),
          F.hom.hom.map κ ≫ φ = localComp (e k) (β k) W a s ha ≫ G.hom.hom.map κ := by
    intro U t
    obtain ⟨V, hV, y, hcovU, hy⟩ := exists_cover_lift e he U t
    let r : ∀ k, F.hom.hom.obj (elt.{u, w} T (V k) ((e k).hom.app _ (y k))) ⟶
        F.hom.hom.obj (elt.{u, w} T U t) := fun k => F.hom.hom.map (eltHom (hV k) (hy k))
    let ζ₁ : ∀ k, F.hom.hom.obj (elt.{u, w} T (V k) ((e k).hom.app _ (y k))) ⟶
        G.hom.hom.obj (elt.{u, w} T U t) := fun k =>
      localComp (e k) (β k) (V k) (y k) _ rfl ≫ G.hom.hom.map (eltHom (hV k) (hy k))
    have hr : ∀ k, 𝒴.val.val.p.IsHomLift (hV k) (r k) := fun k =>
      isHomLift_map_base F (eltHom (hV k) (hy k))
    have hζ₁ : ∀ k, 𝒴.val.val.p.IsHomLift (hV k ≫ 𝟙 U) (ζ₁ k) := fun k => by
      have h₁ := isHomLift_localComp (e k) (β k) (V k) (y k) _ rfl
      have h₂ := isHomLift_map_base G (eltHom.{u, w} (T := T) (hV k) (hy k))
      rw [Category.comp_id]
      exact @IsHomLift.comp_lift_id_left _ _ _ _ _ _ _ _ _ _ (hV k) _ h₂ _ h₁
    obtain ⟨φ, ⟨hφl, hφr⟩, -⟩ := hp.existsUnique_hom_of_cover hV hcovU
      (fun k l => pullback.fst (hV k) (hV l)) (fun k l => pullback.snd (hV k) (hV l))
      (fun k l => IsPullback.of_hasPullback _ _) (𝟙 U) (BasedFunctor.w_obj F.hom.hom _) r
      (BasedFunctor.w_obj G.hom.hom _) ζ₁ (by
        intro k l x₂ r₁ r₂ h₁ h₂ hrr
        let W := pullback (hV k) (hV l)
        let tW : T.obj.obj (Opposite.op W) := T.obj.map (pullback.fst (hV k) (hV l) ≫ hV k).op t
        have hρ₁ : tW = T.obj.map (pullback.fst (hV k) (hV l)).op ((e k).hom.app _ (y k)) := by
          simp only [tW]
          rw [hy k, op_comp, Functor.map_comp_apply]
        have hρ₂ : tW = T.obj.map (pullback.snd (hV k) (hV l)).op ((e l).hom.app _ (y l)) := by
          simp only [tW]
          rw [hy l, ← Functor.map_comp_apply, ← op_comp, pullback.condition]
        let ρ₁ := eltHom.{u, w} (T := T) (pullback.fst (hV k) (hV l)) hρ₁
        let ρ₂ := eltHom.{u, w} (T := T) (pullback.snd (hV k) (hV l)) hρ₂
        have hσ : ρ₁ ≫ eltHom (hV k) (hy k) = ρ₂ ≫ eltHom (hV l) (hy l) :=
          elt_hom_ext pullback.condition
        have := isHomLift_map_base F ρ₁
        have := isHomLift_map_base F ρ₂
        have := isHomLift_map_base F (ρ₁ ≫ eltHom (hV k) (hy k))
        have hc₁ := hg.fill_fac (f := pullback.fst (hV k) (hV l))
          (f' := pullback.fst (hV k) (hV l)) (g := 𝟙 W) (by simp) (F.hom.hom.map ρ₁) r₁
        have hc₂ := hg.fill_fac (f := pullback.snd (hV k) (hV l))
          (f' := pullback.snd (hV k) (hV l)) (g := 𝟙 W) (by simp) (F.hom.hom.map ρ₂) r₂
        have hc₁l := hg.fill_isHomLift (f := pullback.fst (hV k) (hV l))
          (f' := pullback.fst (hV k) (hV l)) (g := 𝟙 W) (by simp) (F.hom.hom.map ρ₁) r₁
        have hc₂l := hg.fill_isHomLift (f := pullback.snd (hV k) (hV l))
          (f' := pullback.snd (hV k) (hV l)) (g := 𝟙 W) (by simp) (F.hom.hom.map ρ₂) r₂
        have hcc := hg.hom_ext (f := pullback.fst (hV k) (hV l) ≫ hV k) (𝟙 W)
          (F.hom.hom.map (ρ₁ ≫ eltHom (hV k) (hy k)))
          (fill_compat_aux F.hom.hom.toFunctor _ _ ρ₁ ρ₂ _ _ r₁ r₂ hc₁ hc₂ hrr hσ)
        have N₁ := localComp_naturality (e k) (β k) ρ₁ (y k) rfl
        have N₂ := (localComp_naturality (e l) (β l) ρ₂ (y l) rfl).trans
          (congrArg (· ≫ G.hom.hom.map ρ₂)
            (hβ' l k W _ ((T' k).obj.map (pullback.fst (hV k) (hV l)).op (y k)) tW _
              (app_map_eq_of_hom (e k) ρ₁ (y k) rfl)))
        exact (congrArg (· ≫ ζ₁ k) hc₁.symm).trans
          ((glue_compat_aux F.hom.hom.toFunctor G.hom.hom.toFunctor _ ρ₁ ρ₂ _ _ _ _ _ N₁ N₂
            hσ).trans ((congrArg (fun c => (c ≫ F.hom.hom.map ρ₂) ≫ ζ₁ l) hcc).trans
              (congrArg (· ≫ ζ₁ l) hc₂))))
    refine ⟨φ, hφl, fun W k' a s ha κ => ?_⟩
    have hcovW := Functor.ofArrows_pullback_fst_mem κ.base hV hcovU
    have hsj : ∀ j, T.obj.map (pullback.fst κ.base (hV j)).op s =
        T.obj.map (pullback.snd κ.base (hV j)).op ((e j).hom.app _ (y j)) := fun j =>
      (congrArg (T.obj.map (pullback.fst κ.base (hV j)).op) (point_eq_of_hom κ)).trans (by
        rw [hy j, ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp,
          pullback.condition])
    let ρ' := fun j => eltHom.{u, w} (T := T) (pullback.fst κ.base (hV j)) (s := T.obj.map
      (pullback.fst κ.base (hV j)).op s) rfl
    let r' := fun j => F.hom.hom.map (ρ' j)
    have hr' : ∀ j, 𝒴.val.val.p.IsHomLift (pullback.fst κ.base (hV j)) (r' j) := fun j =>
      isHomLift_map_base F (ρ' j)
    have := isHomLift_map_base F κ
    have := isHomLift_map_base G κ
    have := isHomLift_localComp (e k') (β k') W a s ha
    refine hom_ext_of_cover_pullback (fun j => pullback.fst κ.base (hV j)) hcovW κ.base
      (BasedFunctor.w_obj F.hom.hom _) r' (BasedFunctor.w_obj G.hom.hom _) fun j => ?_
    let ρ := eltHom.{u, w} (T := T) (pullback.snd κ.base (hV j)) (hsj j)
    have Nv := (localComp_naturality (e j) (β j) ρ (y j) rfl).trans
      (congrArg (· ≫ G.hom.hom.map ρ)
        (hβ' j k' _ _ ((T' k').obj.map (pullback.fst κ.base (hV j)).op a) _ _
          (app_map_eq_of_hom (e k') (ρ' j) a ha)))
    have Nw := localComp_naturality (e k') (β k') (ρ' j) a ha
    exact key_aux F.hom.hom.toFunctor G.hom.hom.toFunctor _ κ ρ (eltHom (hV j) (hy j)) φ _ _ _
      (elt_hom_ext pullback.condition) (hφr j) Nv Nw
  choose φ hφl hφ using key
  let φo : ∀ o : ((algebraicSpaceStackFunctor.{u, w} B S hS).obj T).val.val.obj,
      F.hom.hom.obj o ⟶ G.hom.hom.obj o := fun o => φ o.base o.fiber.as
  have hnat : ∀ (X Y : ((algebraicSpaceStackFunctor.{u, w} B S hS).obj T).val.val.obj)
      (g : X ⟶ Y), F.hom.hom.map g ≫ φo Y = φo X ≫ G.hom.hom.map g := by
    intro X Y g
    obtain ⟨V, hV, y, hcov, hy⟩ := exists_cover_lift e he X.base X.fiber.as
    have := isHomLift_map_base F g
    have := isHomLift_map_base G g
    have : 𝒴.val.val.p.IsHomLift (𝟙 X.base) (φo X) := hφl _ _
    have : 𝒴.val.val.p.IsHomLift (𝟙 Y.base) (φo Y) := hφl _ _
    let r : ∀ k, F.hom.hom.obj (elt.{u, w} T (V k) ((e k).hom.app _ (y k))) ⟶ F.hom.hom.obj X :=
      fun k => F.hom.hom.map (eltHom.{u, w} (T := T) (hV k) (hy k))
    have hr : ∀ k, 𝒴.val.val.p.IsHomLift (hV k) (r k) := fun k =>
      isHomLift_map_base F (eltHom (hV k) (hy k))
    refine hom_ext_of_cover_pullback hV hcov g.base (BasedFunctor.w_obj F.hom.hom _) r
      (BasedFunctor.w_obj G.hom.hom _) fun k => ?_
    exact nat_aux F.hom.hom.toFunctor G.hom.hom.toFunctor (eltHom (hV k) (hy k)) g _ _ _
      (hφ Y.base Y.fiber.as (V k) k (y k) _ rfl (eltHom (hV k) (hy k) ≫ g))
      (hφ X.base X.fiber.as (V k) k (y k) _ rfl (eltHom (hV k) (hy k)))
  let γ : F ⟶ G :=
    ⟨⟨{ app := φo
        naturality := hnat
        isHomLift' := fun o => hφl o.base o.fiber.as }⟩⟩
  refine ⟨γ, fun k => ?_⟩
  apply InducedBicategory.hom₂_ext
  apply InducedBicategory.hom₂_ext
  apply BasedNatTrans.ext
  ext ⟨V, ⟨a⟩⟩
  exact (restrict_aux F.hom.hom.toFunctor G.hom.hom.toFunctor _ _
    (hφ V ((e k).hom.app _ a) V k a _ rfl (𝟙 _))).trans (localComp_self (e k) (β k) V a)

/-- **Composing along the two sides of a commutative square gives the same 1-morphism.** For
morphisms of algebraic spaces with `p₁ ≫ e₁ = p₂ ≫ e₂` and a 1-morphism `F` out of the common
target, `p₁^* e₁^* F = p₂^* e₂^* F` in the 2-category of algebraic stacks. Stated as a term so
that it can be used where rewriting 1-morphism composites is not type-correct. -/
theorem map_comp_comp_eq_of_comp_eq {Z T₁ T₂ : AlgebraicSpaces B S hS} (p₁ : Z ⟶ T₁)
    (p₂ : Z ⟶ T₂) (e₁ : T₁ ⟶ T) (e₂ : T₂ ⟶ T) (h : p₁ ≫ e₁ = p₂ ≫ e₂)
    (F : (algebraicSpaceStackFunctor.{u, w} B S hS).obj T ⟶ 𝒴) :
    (algebraicSpaceStackFunctor.{u, w} B S hS).map p₁ ≫
        ((algebraicSpaceStackFunctor.{u, w} B S hS).map e₁ ≫ F) =
      (algebraicSpaceStackFunctor.{u, w} B S hS).map p₂ ≫
        ((algebraicSpaceStackFunctor.{u, w} B S hS).map e₂ ≫ F) :=
  ((Bicategory.Strict.assoc _ _ _).symm.trans (congrArg (· ≫ F)
    (((algebraicSpaceStackFunctor.{u, w} B S hS).map_comp p₁ e₁).symm.trans
      ((congrArg (algebraicSpaceStackFunctor.{u, w} B S hS).map h).trans
        ((algebraicSpaceStackFunctor.{u, w} B S hS).map_comp p₂ e₂))))).trans
    (Bicategory.Strict.assoc _ _ _)

/-- The component at an object of the transport 2-morphism along an equality of 1-morphisms is
the transport along the induced equality of objects. -/
theorem eqToHom_hom_hom_app {T₀ : AlgebraicSpaces B S hS}
    {F₁ F₂ : (algebraicSpaceStackFunctor.{u, w} B S hS).obj T₀ ⟶ 𝒴} (H : F₁ = F₂)
    (o : ((algebraicSpaceStackFunctor.{u, w} B S hS).obj T₀).val.val.obj) :
    (eqToHom H).hom.hom.app o = eqToHom (congrArg (fun F => F.hom.hom.obj o) H) := by
  subst H
  rfl

/-- The base of a transport morphism of the category of elements is an identity. -/
theorem eqToHom_base {X Y : ((algebraicSpaceStackFunctor.{u, w} B S hS).obj T).val.val.obj}
    (h : X = Y) : (eqToHom h).base = eqToHom (congrArg (fun X => X.base) h) := by
  subst h
  rfl

/-- Bookkeeping for transporting a transported component, for plain functors. -/
theorem transport_eqToHom_aux {C D : Type*} [Category C] [Category D] (F G : C ⥤ D)
    {Y X₁ X₂ : C} (hX : X₁ = X₂) (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) (g₁ : X₁ ⟶ Y) (g₂ : X₂ ⟶ Y)
    (φ : F.obj X₂ ⟶ G.obj X₂) (h₁ : f₁ ≫ eqToHom hX = f₂) (h₂ : eqToHom hX.symm ≫ g₁ = g₂) :
    F.map f₁ ≫ (eqToHom (congrArg F.obj hX) ≫ φ ≫ eqToHom (congrArg G.obj hX).symm) ≫
        G.map g₁ = F.map f₂ ≫ φ ≫ G.map g₂ := by
  subst hX h₁ h₂
  simp

/-- **2-morphisms out of an algebraic space glue along an étale covering, with the compatibility
asked on cartesian squares.** The form of
`AlgebraicGeometry.Stack.exists_hom₂_of_isEtaleCovering` whose hypothesis is that the whiskerings
of `β k` and `β l` along the two projections of a fibre product `Z k l = T k ×_T T l` agree, up to
the identifications of the 1-morphisms of the two sides. -/
theorem exists_hom₂_of_isEtaleCovering_of_isPullback {K : Type v}
    {T' : K → AlgebraicSpaces B S hS} (e : ∀ k, T' k ⟶ T)
    (he : Space.IsEtaleCovering B S hS (fun k => (T' k).obj) (fun k => (e k).hom))
    (β : ∀ k, (algebraicSpaceStackFunctor.{u, w} B S hS).map (e k) ≫ F ⟶
      (algebraicSpaceStackFunctor.{u, w} B S hS).map (e k) ≫ G)
    (Z : K → K → AlgebraicSpaces B S hS) (p₁ : ∀ k l, Z k l ⟶ T' k) (p₂ : ∀ k l, Z k l ⟶ T' l)
    (hZ : ∀ k l, IsPullback (p₁ k l) (p₂ k l) (e k) (e l))
    (hβ : ∀ k l, (algebraicSpaceStackFunctor.{u, w} B S hS).map (p₁ k l) ◁ β k =
      eqToHom (map_comp_comp_eq_of_comp_eq _ _ _ _ (hZ k l).w F) ≫
        ((algebraicSpaceStackFunctor.{u, w} B S hS).map (p₂ k l) ◁ β l) ≫
          eqToHom (map_comp_comp_eq_of_comp_eq _ _ _ _ (hZ k l).w G).symm) :
    ∃ γ : F ⟶ G, ∀ k, (algebraicSpaceStackFunctor.{u, w} B S hS).map (e k) ◁ γ = β k := by
  refine exists_hom₂_of_isEtaleCovering e he β fun k l V a b hab => ?_
  have hZp := AlgebraicSpaces.isPullback_hom B S hS (hZ k l)
  have hw : yonedaEquiv.symm a ≫ (e k).hom = yonedaEquiv.symm b ≫ (e l).hom := by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply, hab]
  set c := yonedaEquiv (hZp.lift _ _ hw)
  have hc₁ : (p₁ k l).hom.app _ c = a := by
    rw [← yonedaEquiv_comp, hZp.lift_fst, Equiv.apply_symm_apply]
  have hc₂ : (p₂ k l).hom.app _ c = b := by
    rw [← yonedaEquiv_comp, hZp.lift_snd, Equiv.apply_symm_apply]
  clear_value c
  subst hc₁ hc₂
  have hcomp := congrArg (fun γ => γ.hom.hom.app (elt.{u, w} (Z k l) V c)) (hβ k l)
  have hX : elt.{u, w} T V ((e k).hom.app _ ((p₁ k l).hom.app _ c)) =
      elt.{u, w} T V ((e l).hom.app _ ((p₂ k l).hom.app _ c)) :=
    congrArg (elt.{u, w} T V) hab
  have h2 : (β k).hom.hom.app (elt.{u, w} (T' k) V ((p₁ k l).hom.app _ c)) =
      eqToHom (congrArg F.hom.hom.obj hX) ≫
        (β l).hom.hom.app (elt.{u, w} (T' l) V ((p₂ k l).hom.app _ c)) ≫
          eqToHom (congrArg G.hom.hom.obj hX).symm :=
    hcomp.trans (congrArg₂ (· ≫ ·) (eqToHom_hom_hom_app _ _)
      (congrArg₂ (· ≫ ·) rfl (eqToHom_hom_hom_app _ _)))
  have hb₁ : eltHom.{u, w} (T := T) (𝟙 V) (eq_map_id hab.symm) ≫ eqToHom hX =
      eltHom.{u, w} (T := T) (𝟙 V) (eq_map_id (rfl : (e l).hom.app _ ((p₂ k l).hom.app _ c) = _)) :=
    elt_hom_ext ((congrArg (fun t => 𝟙 V ≫ t) ((eqToHom_base hX).trans (eqToHom_refl _ _))).trans
      (Category.comp_id _))
  have hb₂ : eqToHom hX.symm ≫ eltHom.{u, w} (T := T) (𝟙 V) (eq_map_id hab) =
      eltHom.{u, w} (T := T) (𝟙 V) (eq_map_id (rfl : (e l).hom.app _ ((p₂ k l).hom.app _ c) = _)) :=
    elt_hom_ext ((congrArg (fun t => t ≫ 𝟙 V) ((eqToHom_base hX.symm).trans
      (eqToHom_refl _ _))).trans (Category.id_comp _))
  unfold localComp
  rw [h2]
  exact transport_eqToHom_aux F.hom.hom.toFunctor G.hom.hom.toFunctor hX _ _ _ _ _ hb₁ hb₂

end Glue

end AlgebraicGeometry.Stack

end
