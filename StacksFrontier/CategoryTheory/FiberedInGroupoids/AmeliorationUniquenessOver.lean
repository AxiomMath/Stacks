module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Factorization
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Fibrewise

/-!
# Uniqueness of the amelioration of a 1-morphism of fibred categories

Stacks 06N8 (Lemma 4.35.17): let `F : 𝒳 ⥤ 𝒴` be a 1-morphism of categories fibred in groupoids
over `𝒞`, and suppose given a 2-commutative diagram `𝒳' ⟵[a] 𝒳 ⟶[b] 𝒳''`, `f : 𝒳' ⥤ 𝒴`,
`g : 𝒳'' ⥤ 𝒴` over `𝒞`, with `a`, `b` equivalences over `𝒞` and `f`, `g` fibred in groupoids.
Then there is an equivalence `h : 𝒳'' ⥤ 𝒳'` of categories over `𝒴` such that `h ∘ b` is
2-isomorphic to `a` as 1-morphisms over `𝒞`; if the diagram commutes, the 2-isomorphism can be
taken over `𝒴`. So the factorization produced by Stacks 06N7 is unique up to equivalence over
`𝒴`.

Categories over a base are functors (structure functors), 1-morphisms over the base commute
strictly with them, 2-morphisms over the base have components lying over identities
(`Functor.IsVerticalNatTrans`), and an equivalence over the base is
`Functor.IsEquivalenceOver`.

## Main results

* `CategoryTheory.Functor.IsFiberedInGroupoids.exists_comp_eq_of_iso`: a functor `h₀` to a
  category fibred in groupoids `f : 𝒳' ⥤ 𝒴` with `h₀ ⋙ f ≅ g` is isomorphic to a functor `h`
  with `h ⋙ f = g` strictly, through an isomorphism whose components lie over those of the
  given one (they are lifts, hence strongly cartesian, hence isomorphisms).
* `CategoryTheory.Functor.IsFiberedInGroupoids.amelioration_unique_isEquivalenceOver`: Stacks
  06N8, first claim.
* `CategoryTheory.Functor.IsFiberedInGroupoids.amelioration_unique_isEquivalenceOver_of_comp_eq`:
  Stacks 06N8, second claim.
* `amelioration_unique` (in `StacksFrontier.CategoryTheory.FiberedInGroupoids.AmeliorationUniqueness`):
  the underlying statement about bare categories, with no strictness.

## Implementation notes

The source compares both `𝒳'` and `𝒳''` with the 2-fibre product `𝒳 ×_{F, 𝒴, id} 𝒴`. The proof
here goes directly: `h₀ = b⁻¹ ⋙ a` satisfies `h₀ ⋙ f ≅ g`, and strongly cartesian lifts along
`f` rectify it to a functor `h` with `h ⋙ f = g`. The quasi-inverse `b⁻¹` is taken from an
adjoint equivalence, whose triangle identity makes the resulting 2-isomorphism `b ⋙ h ≅ a` lie
over `β ≫ α⁻¹` (the two given 2-isomorphisms `b ⋙ g ≅ F ≅ a ⋙ f`), hence over identities of `𝒞`,
and over identities of `𝒴` when the diagram commutes. The 1-morphism `h` is then an equivalence
over `𝒴` by Stacks 003Z (2).
-/

@[expose] public section

open CategoryTheory

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

namespace CategoryTheory.Functor.IsFiberedInGroupoids

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞]
    {𝒳 : Type u₂} [Category.{v₂} 𝒳]
    {𝒴 : Type u₃} [Category.{v₃} 𝒴]
    {𝒳' : Type u₄} [Category.{v₄} 𝒳']
    {𝒳'' : Type u₅} [Category.{v₅} 𝒳'']

/-- A morphism lying over an identity lies over the identity of the image of its source. -/
private theorem isHomLift_id_obj_source {𝒮 : Type*} {𝒟 : Type*} [Category 𝒮] [Category 𝒟]
    (s : 𝒮 ⥤ 𝒟) {R : 𝒟} {x y : 𝒮} {φ : x ⟶ y} (hφ : s.IsHomLift (𝟙 R) φ) :
    s.IsHomLift (𝟙 (s.obj x)) φ := by
  obtain rfl := IsHomLift.domain_eq s (𝟙 R) φ
  exact hφ

/-- A morphism lying, for `f`, over a morphism that lies over an identity for `q`, lies over an
identity for `f ⋙ q`. -/
private theorem isHomLift_comp_id {𝒮 : Type*} {𝒯 : Type*} {𝒟 : Type*} [Category 𝒮]
    [Category 𝒯] [Category 𝒟] (f : 𝒮 ⥤ 𝒯) (q : 𝒯 ⥤ 𝒟) {x y : 𝒮} {u v : 𝒯} (ψ : u ⟶ v)
    (θ : x ⟶ y) [f.IsHomLift ψ θ] [q.IsHomLift (𝟙 (q.obj u)) ψ] :
    (f ⋙ q).IsHomLift (𝟙 ((f ⋙ q).obj x)) θ := by
  obtain ⟨huv, hψ⟩ := (IsHomLift.id_iff_exists_eqToHom q ψ).1 inferInstance
  have hx : f.obj x = u := IsHomLift.domain_eq f ψ θ
  have hy : f.obj y = v := IsHomLift.codomain_eq f ψ θ
  refine (IsHomLift.id_iff_exists_eqToHom (f ⋙ q) θ).2 ⟨by simp [hx, hy, huv], ?_⟩
  rw [Functor.comp_map, IsHomLift.fac' f ψ θ, q.map_comp, q.map_comp, hψ, eqToHom_map,
    eqToHom_map, eqToHom_trans, eqToHom_trans]

/-- A morphism lying over an `eqToHom` lies over an identity. -/
private theorem isHomLift_id_of_eqToHom {𝒮 : Type*} {𝒟 : Type*} [Category 𝒮] [Category 𝒟]
    (s : 𝒮 ⥤ 𝒟) {R T : 𝒟} {e : R = T} {x y : 𝒮} {φ : x ⟶ y} (hφ : s.IsHomLift (eqToHom e) φ) :
    s.IsHomLift (𝟙 (s.obj x)) φ := by
  have := hφ
  have hx : s.obj x = R := IsHomLift.domain_eq s (eqToHom e) φ
  have hy : s.obj y = T := IsHomLift.codomain_eq s (eqToHom e) φ
  refine (IsHomLift.id_iff_exists_eqToHom s φ).2 ⟨by rw [hx, hy, e], ?_⟩
  rw [IsHomLift.fac' s (eqToHom e) φ]
  simp

/-- An equivalence of categories `G` strictly over the base between categories fibred in
groupoids is an equivalence over the base (Stacks 003Z (2)), packaged as
`Functor.IsEquivalenceOver`. -/
private theorem nonempty_isEquivalenceOver {S : Type*} {S' : Type*} [Category S] [Category S']
    {C : Type*} [Category C] {p : S ⥤ C} {p' : S' ⥤ C} (hp : p.IsFiberedInGroupoids)
    (hp' : p'.IsFiberedInGroupoids) (G : S ⥤ S') (hG : G ⋙ p' = p) (hGe : G.IsEquivalence) :
    Nonempty (IsEquivalenceOver p p' G) := by
  obtain ⟨K, hK, η, ε, hη, hε⟩ := isEquivalence_over p p' hp hp' G hG hGe
  exact ⟨{
    inv := K
    inv_over := hK
    unitIso := η
    counitIso := ε
    unit_vertical := fun x => isHomLift_id_obj_source p (hη x)
    counit_vertical := fun x => isHomLift_id_obj_source p' (hε x) }⟩

/-- **Rectification along a category fibred in groupoids.** Let `f : 𝒳' ⥤ 𝒴` be fibred in
groupoids, `h₀ : 𝒵 ⥤ 𝒳'` a functor and `γ : g ≅ h₀ ⋙ f` an isomorphism. Then there is a
functor `h : 𝒵 ⥤ 𝒳'` with `h ⋙ f = g` strictly, and an isomorphism `ε : h ≅ h₀` whose
component at `z` lies over `γ.hom.app z`. The component at `z` is a lift of `γ.hom.app z` to
`h₀.obj z`; it is strongly cartesian over an isomorphism, hence an isomorphism. -/
theorem exists_comp_eq_of_iso {𝒵 : Type*} [Category 𝒵] {f : 𝒳' ⥤ 𝒴}
    (hf : f.IsFiberedInGroupoids) (h₀ : 𝒵 ⥤ 𝒳') {g : 𝒵 ⥤ 𝒴} (γ : g ≅ h₀ ⋙ f) :
    ∃ (h : 𝒵 ⥤ 𝒳') (_ : h ⋙ f = g) (ε : h ≅ h₀),
      ∀ z, f.IsHomLift (γ.hom.app z) (ε.hom.app z) := by
  choose y φ hφ using fun z => hf.exists_lift (γ.hom.app z) (h₀.obj z) rfl
  have hiso (z : 𝒵) : IsIso (φ z) := by
    have := hφ z
    have := hf.isStronglyCartesian_homLift (γ.hom.app z) (φ z)
    exact IsStronglyCartesian.isIso_of_base_isIso f (γ.hom.app z) (φ z)
  have hy (z : 𝒵) : f.obj (y z) = g.obj z := by
    have := hφ z
    exact IsHomLift.domain_eq f (γ.hom.app z) (φ z)
  have hmap (z : 𝒵) : f.map (φ z) = eqToHom (hy z) ≫ γ.hom.app z := by
    have := hφ z
    simpa using IsHomLift.fac' f (γ.hom.app z) (φ z)
  refine ⟨h₀.copyObj y fun z => (asIso (φ z)).symm, Functor.ext hy fun z z' m => ?_,
    (h₀.isoCopyObj y fun z => (asIso (φ z)).symm).symm, fun z => ?_⟩
  · have hnat := NatIso.naturality_2 γ m
    simp only [Functor.comp_map] at hnat
    simp only [Functor.comp_map, Functor.copyObj, Iso.symm_inv, Iso.symm_hom, asIso_hom,
      asIso_inv, Functor.map_comp, Functor.map_inv, hmap, IsIso.inv_comp, inv_eqToHom,
      Category.assoc]
    rw [← hnat]
    simp
  · change f.IsHomLift (γ.hom.app z) (φ z)
    exact hφ z

/-- The common core of both claims of Stacks 06N8: with `a`, `b` equivalences and `f` fibred in
groupoids, a pair of isomorphisms `α : a ⋙ f ≅ F`, `β : b ⋙ g ≅ F` yields an equivalence
`h : 𝒳'' ⥤ 𝒳'` with `h ⋙ f = g` strictly and an isomorphism `θ : b ⋙ h ≅ a` whose component
at `x` lies, for `f`, over `β.hom.app x ≫ α.inv.app x`. The equivalence `e` with functor `b`
supplies the quasi-inverse; its triangle identity is what the lift condition rests on. -/
theorem exists_comp_eq_isEquivalence_of_iso (F : 𝒳 ⥤ 𝒴) (a : 𝒳 ⥤ 𝒳') (b : 𝒳 ⥤ 𝒳'')
    (e : 𝒳 ≌ 𝒳'') (heb : e.functor = b) (f : 𝒳' ⥤ 𝒴) (g : 𝒳'' ⥤ 𝒴) [a.IsEquivalence]
    (hf : f.IsFiberedInGroupoids) (α : a ⋙ f ≅ F) (β : b ⋙ g ≅ F) :
    ∃ (h : 𝒳'' ⥤ 𝒳') (_ : h ⋙ f = g) (_ : h.IsEquivalence) (θ : b ⋙ h ≅ a),
      ∀ x, f.IsHomLift (β.hom.app x ≫ α.inv.app x) (θ.hom.app x) := by
  subst heb
  let γ : g ≅ (e.inverse ⋙ a) ⋙ f :=
    (Functor.leftUnitor g).symm ≪≫ Functor.isoWhiskerRight e.counitIso.symm g ≪≫
      Functor.associator e.inverse e.functor g ≪≫ Functor.isoWhiskerLeft e.inverse (β ≪≫ α.symm) ≪≫
      (Functor.associator e.inverse a f).symm
  obtain ⟨h, hh, ε, hε⟩ := exists_comp_eq_of_iso hf (e.inverse ⋙ a) γ
  have : h.IsEquivalence := Functor.isEquivalence_of_iso ε.symm
  let θ : e.functor ⋙ h ≅ a :=
    Functor.isoWhiskerLeft e.functor ε ≪≫ (Functor.associator e.functor e.inverse a).symm ≪≫
      Functor.isoWhiskerRight e.unitIso.symm a ≪≫ Functor.leftUnitor a
  refine ⟨h, hh, this, θ, fun x => ?_⟩
  have hθ : θ.hom.app x = ε.hom.app (e.functor.obj x) ≫ a.map (e.unitInv.app x) := by
    simp [θ]
  have htri : e.counitIso.inv.app (e.functor.obj x) ≫ e.functor.map (e.unitInv.app x) = 𝟙 _ :=
    e.counitInv_functor_comp x
  have h1 := α.inv.naturality (e.unitInv.app x)
  have h2 := β.hom.naturality (e.unitInv.app x)
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at h1 h2
  have hcomp : γ.hom.app (e.functor.obj x) ≫ f.map (a.map (e.unitInv.app x)) =
      β.hom.app x ≫ α.inv.app x := by
    simp only [γ, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.leftUnitor_inv_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id, Category.assoc]
    rw [← h1, ← reassoc_of% h2, ← g.map_comp_assoc, htri, g.map_id, Category.id_comp]
  have := hε (e.functor.obj x)
  rw [hθ, ← hcomp]
  infer_instance

/-- **Stacks 06N8 (Lemma 4.35.17), first claim.** Let `p : 𝒳 ⥤ 𝒞` and `q : 𝒴 ⥤ 𝒞` be fibred
in groupoids and `F : 𝒳 ⥤ 𝒴` a 1-morphism over `𝒞` (`F ⋙ q = p`). Let `p' : 𝒳' ⥤ 𝒞`,
`p'' : 𝒳'' ⥤ 𝒞` be categories over `𝒞`, `a : 𝒳 ⥤ 𝒳'` and `b : 𝒳 ⥤ 𝒳''` equivalences over
`𝒞` (`a ⋙ p' = p`, `b ⋙ p'' = p`, with quasi-inverses, units and counits over `𝒞`), and
`f : 𝒳' ⥤ 𝒴`, `g : 𝒳'' ⥤ 𝒴` 1-morphisms over `𝒞` (`f ⋙ q = p'`, `g ⋙ q = p''`) which are
fibred in groupoids. Assume the diagram 2-commutes over `𝒞`: `α : a ⋙ f ≅ F` and
`β : b ⋙ g ≅ F` have components over identities of `𝒞`. Then there is an equivalence
`h : 𝒳'' ⥤ 𝒳'` of categories over `𝒴` (`h ⋙ f = g` and `Functor.IsEquivalenceOver g f h`)
together with a 2-isomorphism `b ⋙ h ≅ a` of 1-morphisms over `𝒞` (components over identities
of `𝒞` for `p'`).

The fibredness of `p` and `q` and the equation `F ⋙ q = p` are part of the setting of the
source and are not used by the proof. -/
@[stacks 06N8 "first claim: an equivalence h over 𝒴 with h ∘ b ≅ a over 𝒞"]
theorem amelioration_unique_isEquivalenceOver {p : 𝒳 ⥤ 𝒞} {q : 𝒴 ⥤ 𝒞} {p' : 𝒳' ⥤ 𝒞}
    {p'' : 𝒳'' ⥤ 𝒞} (_hp : p.IsFiberedInGroupoids) (_hq : q.IsFiberedInGroupoids)
    (F : 𝒳 ⥤ 𝒴) (_hF : F ⋙ q = p)
    (a : 𝒳 ⥤ 𝒳') (b : 𝒳 ⥤ 𝒳'') (_ha : a ⋙ p' = p) (_hb : b ⋙ p'' = p)
    (ea : IsEquivalenceOver p p' a) (eb : IsEquivalenceOver p p'' b)
    (f : 𝒳' ⥤ 𝒴) (g : 𝒳'' ⥤ 𝒴) (hfq : f ⋙ q = p') (_hgq : g ⋙ q = p'')
    (hf : f.IsFiberedInGroupoids) (hg : g.IsFiberedInGroupoids)
    (α : a ⋙ f ≅ F) (hα : IsVerticalNatTrans q α.hom)
    (β : b ⋙ g ≅ F) (hβ : IsVerticalNatTrans q β.hom) :
    ∃ (h : 𝒳'' ⥤ 𝒳') (_ : h ⋙ f = g) (_ : Nonempty (IsEquivalenceOver g f h))
      (θ : b ⋙ h ≅ a), IsVerticalNatTrans p' θ.hom := by
  have : a.IsEquivalence :=
    (Equivalence.mk a ea.inv ea.unitIso.symm ea.counitIso).isEquivalence_functor
  have : b.IsEquivalence :=
    (Equivalence.mk b eb.inv eb.unitIso.symm eb.counitIso).isEquivalence_functor
  obtain ⟨h, hh, he, θ, hθ⟩ :=
    exists_comp_eq_isEquivalence_of_iso F a b b.asEquivalence rfl f g hf α β
  refine ⟨h, hh, nonempty_isEquivalenceOver hg hf h hh he, θ, fun x => ?_⟩
  have := hθ x
  have := hβ x
  have : q.IsHomLift (𝟙 (q.obj (F.obj x))) (α.inv.app x) :=
    (IsHomLift.id_iff_exists_eqToHom q _).2 (by
      obtain ⟨e, he⟩ := (IsHomLift.id_iff_exists_eqToHom q _).1 (hα x)
      refine ⟨e.symm, ?_⟩
      rw [← cancel_mono (q.map (α.hom.app x)), ← q.map_comp, Iso.inv_hom_id_app, he]
      simp)
  have : q.IsHomLift (𝟙 (q.obj ((b ⋙ g).obj x))) (β.hom.app x ≫ α.inv.app x) := by
    obtain ⟨e₁, h₁⟩ := (IsHomLift.id_iff_exists_eqToHom q _).1 (hβ x)
    obtain ⟨e₂, h₂⟩ := (IsHomLift.id_iff_exists_eqToHom q _).1 this
    exact (IsHomLift.id_iff_exists_eqToHom q _).2 ⟨e₁.trans e₂, by simp [h₁, h₂]⟩
  subst hfq
  exact isHomLift_comp_id f q (β.hom.app x ≫ α.inv.app x) (θ.hom.app x)

/-- **Stacks 06N8 (Lemma 4.35.17), second claim.** In the setting of
`amelioration_unique_isEquivalenceOver`, if the diagram actually commutes (`a ⋙ f = F` and
`b ⋙ g = F`), then the equivalence `h : 𝒳'' ⥤ 𝒳'` over `𝒴` can be chosen so that `b ⋙ h ≅ a`
is a 2-isomorphism of 1-morphisms over `𝒴`: its components lie over identities of `𝒴` for `f`
(and hence over identities of `𝒞` for `p' = f ⋙ q`).

The fibredness of `p` and `q`, the equation `F ⋙ q = p`, and the remaining equations over `𝒞`
are part of the setting of the source and are not used by the proof. -/
@[stacks 06N8 "second claim: if the diagram commutes, h ∘ b ≅ a over 𝒴"]
theorem amelioration_unique_isEquivalenceOver_of_comp_eq {p : 𝒳 ⥤ 𝒞} {q : 𝒴 ⥤ 𝒞}
    {p' : 𝒳' ⥤ 𝒞} {p'' : 𝒳'' ⥤ 𝒞} (_hp : p.IsFiberedInGroupoids)
    (_hq : q.IsFiberedInGroupoids) (F : 𝒳 ⥤ 𝒴) (_hF : F ⋙ q = p)
    (a : 𝒳 ⥤ 𝒳') (b : 𝒳 ⥤ 𝒳'') (_ha : a ⋙ p' = p) (_hb : b ⋙ p'' = p)
    (ea : IsEquivalenceOver p p' a) (eb : IsEquivalenceOver p p'' b)
    (f : 𝒳' ⥤ 𝒴) (g : 𝒳'' ⥤ 𝒴) (hfq : f ⋙ q = p') (_hgq : g ⋙ q = p'')
    (hf : f.IsFiberedInGroupoids) (hg : g.IsFiberedInGroupoids)
    (hα : a ⋙ f = F) (hβ : b ⋙ g = F) :
    ∃ (h : 𝒳'' ⥤ 𝒳') (_ : h ⋙ f = g) (_ : Nonempty (IsEquivalenceOver g f h))
      (θ : b ⋙ h ≅ a), IsVerticalNatTrans f θ.hom ∧ IsVerticalNatTrans p' θ.hom := by
  have : a.IsEquivalence :=
    (Equivalence.mk a ea.inv ea.unitIso.symm ea.counitIso).isEquivalence_functor
  have : b.IsEquivalence :=
    (Equivalence.mk b eb.inv eb.unitIso.symm eb.counitIso).isEquivalence_functor
  obtain ⟨h, hh, he, θ, hθ⟩ :=
    exists_comp_eq_isEquivalence_of_iso F a b b.asEquivalence rfl f g hf (eqToIso hα)
      (eqToIso hβ)
  have hY : IsVerticalNatTrans f θ.hom := fun x => by
    have := hθ x
    simp only [eqToIso.hom, eqToIso.inv, eqToHom_app, eqToHom_trans] at this
    exact isHomLift_id_of_eqToHom f this
  refine ⟨h, hh, nonempty_isEquivalenceOver hg hf h hh he, θ, hY, fun x => ?_⟩
  have := hY x
  have : q.IsHomLift (𝟙 (q.obj (f.obj ((b ⋙ h).obj x))))
      (f.map (θ.hom.app x)) := by
    obtain ⟨e, he⟩ := (IsHomLift.id_iff_exists_eqToHom f _).1 (hY x)
    refine (IsHomLift.id_iff_exists_eqToHom q _).2 ⟨congrArg q.obj e, ?_⟩
    rw [he, eqToHom_map]
  subst hfq
  exact isHomLift_comp_id f q (f.map (θ.hom.app x)) (θ.hom.app x)

end CategoryTheory.Functor.IsFiberedInGroupoids
