module

public import StacksFrontier.Deformation.InfinitesimalAutomorphism.Basic.Object

/-!
# Independence of infinitesimal automorphisms from choices

The independence of infinitesimal automorphisms from the chosen pushforward (Tag 06JR), the
automorphisms at a point of a predeformation category, the independence of the chosen point,
and the infinitesimal automorphism group of a predeformation category (Tag 06JS).
-/

@[expose] public section

namespace Deformation

/-! ### Independence of infinitesimal automorphisms from pushforward choices -/

section
open CategoryTheory
universe v₁ v₂ u₁ u₂ u v w

/-- Pushforwards of isomorphic objects along the same arrow have a unique
isomorphism commuting with their structure maps. -/
@[stacks 06JR "canonical isomorphism of pushforwards"]
public theorem existsUnique_pushforwardIso
    {F : Type u₁} [Category.{v₁} F]
    {C : Type u₂} [Category.{v₂} C] {p : F ⥤ C}
    {A₀ A : C} {x₀ y₀ : p.Fiber A₀} {x y : p.Fiber A}
    (hp : IsCofiberedInGroupoids p)
    (g : A₀ ⟶ A) (h₀ : x₀ ≅ y₀)
    (i : x₀.1 ⟶ x.1) (hi : p.IsHomLift g i)
    (j : y₀.1 ⟶ y.1) (hj : p.IsHomLift g j) :
    ∃! h : x ≅ y, i ≫ h.hom.val = h₀.hom.val ≫ j := by
  classical
  let := isStronglyCocartesian_of_isCofiberedInGroupoids hp g i hi
  let := isStronglyCocartesian_of_isCofiberedInGroupoids hp g j hj
  let : p.IsHomLift (𝟙 A₀) h₀.hom.val := h₀.hom.2
  let : p.IsHomLift g (h₀.hom.val ≫ j) := IsHomLift.comp_lift_id_left p g j h₀.hom.val
  let hom := Functor.IsStronglyCocartesian.map p g i (Category.comp_id g).symm
    (h₀.hom.val ≫ j)
  let : p.IsHomLift (𝟙 A) hom :=
    Functor.IsStronglyCocartesian.map_isHomLift p g i (Category.comp_id g).symm
      (h₀.hom.val ≫ j)
  have hfac : i ≫ hom = h₀.hom.val ≫ j :=
    Functor.IsStronglyCocartesian.fac p g i (Category.comp_id g).symm (h₀.hom.val ≫ j)
  let : p.IsHomLift (𝟙 A₀) h₀.inv.val := h₀.inv.2
  let : p.IsHomLift g (h₀.inv.val ≫ i) := IsHomLift.comp_lift_id_left p g i h₀.inv.val
  let inv := Functor.IsStronglyCocartesian.map p g j (Category.comp_id g).symm
    (h₀.inv.val ≫ i)
  let : p.IsHomLift (𝟙 A) inv :=
    Functor.IsStronglyCocartesian.map_isHomLift p g j (Category.comp_id g).symm
      (h₀.inv.val ≫ i)
  have hifac : j ≫ inv = h₀.inv.val ≫ i :=
    Functor.IsStronglyCocartesian.fac p g j (Category.comp_id g).symm (h₀.inv.val ≫ i)
  have h₀_hom_inv : h₀.hom.val ≫ h₀.inv.val = 𝟙 x₀.1 :=
    congrArg (fun f : x₀ ⟶ x₀ => f.val) h₀.hom_inv_id
  have h₀_inv_hom : h₀.inv.val ≫ h₀.hom.val = 𝟙 y₀.1 :=
    congrArg (fun f : y₀ ⟶ y₀ => f.val) h₀.inv_hom_id
  have hhom_inv : hom ≫ inv = 𝟙 x.1 := by
    let : p.IsHomLift (𝟙 A) (𝟙 x.1) := IsHomLift.id x.2
    apply Functor.IsStronglyCocartesian.ext (p := p) (f := g) i (𝟙 A)
    rw [← Category.assoc, hfac, Category.assoc, hifac, ← Category.assoc, h₀_hom_inv]
    simp
  have hinv_hom : inv ≫ hom = 𝟙 y.1 := by
    let : p.IsHomLift (𝟙 A) (𝟙 y.1) := IsHomLift.id y.2
    apply Functor.IsStronglyCocartesian.ext (p := p) (f := g) j (𝟙 A)
    rw [← Category.assoc, hifac, Category.assoc, hfac, ← Category.assoc, h₀_inv_hom]
    simp
  let h : x ≅ y :=
    { hom := ⟨hom, inferInstance⟩
      inv := ⟨inv, inferInstance⟩
      hom_inv_id := Functor.Fiber.hom_ext hhom_inv
      inv_hom_id := Functor.Fiber.hom_ext hinv_hom }
  refine ⟨h, hfac, fun h' hh' => Iso.ext <| Functor.Fiber.hom_ext ?_⟩
  show h'.hom.val = h.hom.val
  let : p.IsHomLift (𝟙 A) h'.hom.val := h'.hom.2
  let : p.IsHomLift (𝟙 A) h.hom.val := h.hom.2
  exact Functor.IsStronglyCocartesian.ext (p := p) (f := g) i (𝟙 A) (hh'.trans hfac.symm)

private lemma conjAut_hom_val {C : Type u} [Category.{v₁} C] {D : Type w} [Category.{v} D]
    {p : C ⥤ D} {S : D} {u v : p.Fiber S} (h : u ≅ v) (a : Aut u) :
    (h.conjAut a).asIso.hom.val = h.inv.val ≫ a.asIso.hom.val ≫ h.hom.val :=
  congrArg (fun f : v ≅ v => f.hom.val) (Iso.conjAut_apply h a)

private lemma comp_eq_self_iff_conj_comp_eq_self {F : Type u₁} [Category.{v₁} F]
    {X Y X₀ Y₀ : F} (u : X ≅ Y) (v : X₀ ≅ Y₀) (a : X ⟶ X) (ri : X ⟶ X₀) (rj : Y ⟶ Y₀)
    (h : u.hom ≫ rj = ri ≫ v.hom) :
    a ≫ ri = ri ↔ (u.inv ≫ a ≫ u.hom) ≫ rj = rj := by
  obtain rfl : rj = u.inv ≫ ri ≫ v.hom := by rw [← h, Iso.inv_hom_id_assoc]
  constructor
  · intro ha
    simp [reassoc_of% ha]
  · intro ha
    simpa using congrArg (fun f => u.hom ≫ f ≫ v.inv) ha

private theorem conjugate_mem_infinitesimal_iff
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type u₁} [Category.{v₁} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    {A₀ Aε : ArtinianLocalAlgCat.{u, v, w} Λ k}
    {x₀ y₀ : p.Fiber A₀} {xε yε : p.Fiber Aε}
    (hp : IsCofiberedInGroupoids p)
    (g : A₀ ⟶ Aε) (e : Aε ⟶ A₀)
    (hpair : IsCanonicalDualNumberPair g e)
    (h₀ : x₀ ≅ y₀)
    (i : x₀.1 ⟶ xε.1) (hi : p.IsHomLift g i)
    (j : y₀.1 ⟶ yε.1) (hj : p.IsHomLift g j)
    (h : xε ≅ yε)
    (hsquare : i ≫ h.hom.val = h₀.hom.val ≫ j)
    (a : Aut xε) :
    a ∈ infinitesimalAutomorphisms hp g e hpair i hi ↔
      h.conjAut a ∈ infinitesimalAutomorphisms hp g e hpair j hj := by
  let ri := (canonicalRetraction hp g e hpair.split i hi).1
  let rj := (canonicalRetraction hp g e hpair.split j hj).1
  let := isStronglyCocartesian_of_isCofiberedInGroupoids hp g i hi
  let : p.IsHomLift (𝟙 Aε) h.hom.val := h.hom.2
  let : p.IsHomLift e rj :=
    (canonicalRetraction hp g e hpair.split j hj).2.1
  let : p.IsHomLift e ri :=
    (canonicalRetraction hp g e hpair.split i hi).2.1
  let : p.IsHomLift (𝟙 A₀) h₀.hom.val := h₀.hom.2
  let : p.IsHomLift e (h.hom.val ≫ rj) :=
    IsHomLift.comp_lift_id_left p e rj h.hom.val
  let : p.IsHomLift e (ri ≫ h₀.hom.val) :=
    IsHomLift.comp_lift_id_right p e ri h₀.hom.val
  have hri : h.hom.val ≫ rj = ri ≫ h₀.hom.val := by
    apply Functor.IsStronglyCocartesian.ext (p := p) (f := g) i e
    calc
      i ≫ (h.hom.val ≫ rj) = h₀.hom.val := by
        rw [← Category.assoc, hsquare, Category.assoc,
          (canonicalRetraction hp g e hpair.split j hj).2.2]
        simp
      _ = i ≫ (ri ≫ h₀.hom.val) := by
        rw [← Category.assoc,
          (canonicalRetraction hp g e hpair.split i hi).2.2]
        simp
  rw [mem_infinitesimalAutomorphisms_iff hp g e hpair i hi a,
    mem_infinitesimalAutomorphisms_iff hp g e hpair j hj (h.conjAut a), conjAut_hom_val]
  exact comp_eq_self_iff_conj_comp_eq_self (Functor.Fiber.fiberInclusion.mapIso h)
    (Functor.Fiber.fiberInclusion.mapIso h₀) a.asIso.hom.val ri rj hri

private theorem map_conjAut_infinitesimalAutomorphisms
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type u₁} [Category.{v₁} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    {A₀ Aε : ArtinianLocalAlgCat.{u, v, w} Λ k}
    {x₀ y₀ : p.Fiber A₀} {xε yε : p.Fiber Aε}
    (hp : IsCofiberedInGroupoids p)
    (g : A₀ ⟶ Aε) (e : Aε ⟶ A₀)
    (hpair : IsCanonicalDualNumberPair g e)
    (h₀ : x₀ ≅ y₀)
    (i : x₀.1 ⟶ xε.1) (hi : p.IsHomLift g i)
    (j : y₀.1 ⟶ yε.1) (hj : p.IsHomLift g j)
    (h : xε ≅ yε)
    (hsquare : i ≫ h.hom.val = h₀.hom.val ≫ j) :
    (infinitesimalAutomorphisms hp g e hpair i hi).map (h.conjAut : Aut xε →* Aut yε) =
      infinitesimalAutomorphisms hp g e hpair j hj := by
  ext b
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (conjugate_mem_infinitesimal_iff hp g e hpair h₀ i hi j hj h hsquare a).mp ha
  · intro hb
    exact ⟨h.conjAut.symm b, (conjugate_mem_infinitesimal_iff hp g e hpair h₀ i hi j hj h
      hsquare _).mpr (by simpa using hb), by simp⟩

/-- An isomorphism of the original objects canonically identifies their
infinitesimal automorphism groups, by conjugation through the unique
comparison of their pushforwards. -/
@[stacks 06JR "invariance under isomorphism of the original object"]
public theorem existsUnique_infinitesimalAutomorphismsEquiv
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type u₁} [Category.{v₁} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    {A₀ Aε : ArtinianLocalAlgCat.{u, v, w} Λ k}
    {x₀ y₀ : p.Fiber A₀} {xε yε : p.Fiber Aε}
    (hp : IsCofiberedInGroupoids p)
    (g : A₀ ⟶ Aε) (e : Aε ⟶ A₀)
    (hpair : IsCanonicalDualNumberPair g e)
    (h₀ : x₀ ≅ y₀)
    (i : x₀.1 ⟶ xε.1) (hi : p.IsHomLift g i)
    (j : y₀.1 ⟶ yε.1) (hj : p.IsHomLift g j) :
    ∃! φ : infinitesimalAutomorphisms hp g e hpair i hi ≃*
        infinitesimalAutomorphisms hp g e hpair j hj,
      ∃ h : xε ≅ yε,
        (i ≫ h.hom.val = h₀.hom.val ≫ j) ∧
        (∀ a, (φ a).1 = h.conjAut a.1) := by
  classical
  rcases existsUnique_pushforwardIso hp g h₀ i hi j hj with ⟨h, hfac, huniq⟩
  let S := infinitesimalAutomorphisms hp g e hpair i hi
  let T := infinitesimalAutomorphisms hp g e hpair j hj
  have hmap : S.map (h.conjAut : Aut xε →* Aut yε) = T :=
    map_conjAut_infinitesimalAutomorphisms hp g e hpair h₀ i hi j hj h hfac
  let φ : S ≃* T :=
    (h.conjAut.subgroupMap S).trans (MulEquiv.subgroupCongr hmap)
  have hφ (a : S) : (φ a).1 = h.conjAut a.1 := by
    simp [φ]
  refine ⟨φ, ⟨h, hfac, hφ⟩, ?_⟩
  rintro ψ ⟨h', hfac', hψ⟩
  obtain rfl := huniq h' hfac'
  exact MulEquiv.ext fun a => Subtype.ext ((hψ a).trans (hφ a).symm)

/-- The automorphism group of the original object acts on its infinitesimal
automorphism group by conjugation through pushed-forward automorphisms. -/
@[stacks 06JR "action of automorphisms of the original object"]
public theorem existsUnique_infinitesimalAutomorphismAction
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type u₁} [Category.{v₁} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    {A₀ Aε : ArtinianLocalAlgCat.{u, v, w} Λ k}
    {x₀ : p.Fiber A₀} {xε : p.Fiber Aε}
    (hp : IsCofiberedInGroupoids p)
    (g : A₀ ⟶ Aε) (e : Aε ⟶ A₀)
    (hpair : IsCanonicalDualNumberPair g e)
    (i : x₀.1 ⟶ xε.1) (hi : p.IsHomLift g i) :
    ∃! ρ : Aut x₀ →* MulAut
        (infinitesimalAutomorphisms hp g e hpair i hi),
      ∀ (a : Aut x₀)
        (b : infinitesimalAutomorphisms hp g e hpair i hi),
        ((ρ a) b).1 =
          (pushforwardAutomorphism hp g i hi a).asIso.conjAut b.1 := by
  classical
  let S := infinitesimalAutomorphisms hp g e hpair i hi
  let pushed (a : Aut x₀) := pushforwardAutomorphism hp g i hi a
  let pushedHom := pushforwardAutomorphismHom hp g i hi
  have hsq (a : Aut x₀) : i ≫ (pushed a).asIso.hom.val = a.asIso.hom.val ≫ i := by
    show i ≫ pushforwardEndomorphism hp g i hi a = a.asIso.hom.val ≫ i
    exact (hom_comp_eq_comp_pushforwardEndomorphism hp g i hi a).symm
  have hmap (a : Aut x₀) : S.map ((pushed a).asIso.conjAut : Aut xε →* Aut xε) = S :=
    map_conjAut_infinitesimalAutomorphisms hp g e hpair a.asIso i hi i hi (pushed a).asIso (hsq a)
  let actionEquiv (a : Aut x₀) : S ≃* S :=
    ((pushed a).asIso.conjAut.subgroupMap S).trans (MulEquiv.subgroupCongr (hmap a))
  have actionEquiv_apply (a : Aut x₀) (b : S) :
      (actionEquiv a b).1 = (pushed a).asIso.conjAut b.1 := by
    simp [actionEquiv]
  let ρ : Aut x₀ →* MulAut S := {
    toFun := actionEquiv
    map_one' := by
      apply MulEquiv.ext
      intro b
      apply Subtype.ext
      rw [actionEquiv_apply]
      show (pushed 1).asIso.conjAut b.1 = b.1
      rw [show pushed 1 = (1 : Aut xε) from map_one pushedHom]
      show (Iso.refl xε).conjAut b.1 = b.1
      ext1
      rw [Iso.conjAut_apply, Iso.refl_symm, Iso.refl_trans]
      exact Iso.trans_refl b.1.asIso
    map_mul' a₁ a₂ := by
      apply MulEquiv.ext
      intro b
      apply Subtype.ext
      rw [MulAut.mul_apply, actionEquiv_apply a₁, actionEquiv_apply a₂]
      show (pushed (a₁ * a₂)).asIso.conjAut b.1 =
        (pushed a₁).asIso.conjAut ((pushed a₂).asIso.conjAut b.1)
      rw [show pushed (a₁ * a₂) = pushed a₁ * pushed a₂ from map_mul pushedHom a₁ a₂,
        Aut.mul_asIso]
      exact Iso.trans_conjAut (pushed a₂).asIso (pushed a₁).asIso b.1 }
  exact ⟨ρ, actionEquiv_apply, fun ρ' hρ' => MonoidHom.ext fun a => MulEquiv.ext fun b =>
    Subtype.ext ((hρ' a b).trans (actionEquiv_apply a b).symm)⟩

end

/-! ### Automorphisms at a point of a predeformation category -/

section
open CategoryTheory
universe u v w v₁ u₁

/-- The automorphism group of an object over the residue field in a predeformation
category is trivial. -/
@[stacks 06JS "automorphisms_at_a_point"]
public theorem subsingleton_aut_residueField
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type u₁} [Category.{v₁} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (hp : IsPredeformationCategory p)
    (x₀ : p.Fiber (residueFieldObject Λ k)) :
    Subsingleton (Aut x₀) :=
  let ⟨E⟩ := hp.specialFiber; ⟨fun _ _ => Aut.ext (Iso.ext (E.functor.map_injective (Subsingleton.elim _ _)))⟩

/-- Every automorphism of a pushforward to the dual numbers is infinitesimal. -/
@[stacks 06JS "automorphisms_at_a_point"]
public theorem infinitesimalAutomorphisms_eq_top
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type u₁} [Category.{v₁} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (hp : IsPredeformationCategory p)
    {Aε : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (x₀ : p.Fiber (residueFieldObject Λ k)) (xε : p.Fiber Aε)
    (g : residueFieldObject Λ k ⟶ Aε)
    (e : Aε ⟶ residueFieldObject Λ k)
    (hpair : IsCanonicalDualNumberPair g e)
    (i : x₀.1 ⟶ xε.1) (hi : p.IsHomLift g i) :
    infinitesimalAutomorphisms hp.cofibered g e hpair i hi = ⊤ := by
  refine (Subgroup.eq_top_iff' _).2 fun a => ?_
  show _ = 1
  exact (subsingleton_aut_residueField hp x₀).elim _ _

end

/-! ### Independence of the point for infinitesimal automorphisms -/

section
open CategoryTheory
universe u v w u₁ v₁

/-- Any two points over the residue field in a predeformation category have exactly
one isomorphism between them. -/
@[stacks 06JS "independence_of_point"]
public theorem existsUnique_pointIso
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type u₁} [Category.{v₁} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (hp : IsPredeformationCategory p)
    (x₀ y₀ : p.Fiber (residueFieldObject.{u, v, w} Λ k)) :
    ∃! _ : x₀ ≅ y₀, True := by
  obtain ⟨E⟩ := hp.specialFiber
  exact ⟨E.unitIso.app x₀ ≪≫ E.inverse.mapIso
    (eqToIso (Subsingleton.elim _ _)) ≪≫ (E.unitIso.app y₀).symm, trivial,
    fun _ _ => Iso.ext (E.functor.map_injective (Subsingleton.elim _ _))⟩

/-- The unique isomorphism of points induces the canonical group isomorphism on
infinitesimal automorphisms. Its action is conjugation by any compatible
isomorphism between chosen pushforwards to the dual numbers. -/
@[stacks 06JS "independence_of_point"]
public theorem existsUnique_infinitesimalAutomorphismsEquiv_of_isPredeformationCategory
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type u₁} [Category.{v₁} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (hp : IsPredeformationCategory p)
    {Aε : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (g : residueFieldObject.{u, v, w} Λ k ⟶ Aε)
    (e : Aε ⟶ residueFieldObject.{u, v, w} Λ k)
    (hpair : IsCanonicalDualNumberPair g e)
    (x₀ y₀ : p.Fiber (residueFieldObject.{u, v, w} Λ k))
    (xε yε : p.Fiber Aε)
    (iₓ : x₀.1 ⟶ xε.1) (hiₓ : p.IsHomLift g iₓ)
    (iᵧ : y₀.1 ⟶ yε.1) (hiᵧ : p.IsHomLift g iᵧ) :
    ∃! φ : ↥(infinitesimalAutomorphisms hp.cofibered g e hpair iₓ hiₓ) ≃*
        ↥(infinitesimalAutomorphisms hp.cofibered g e hpair iᵧ hiᵧ),
      ∀ (f : x₀ ≅ y₀) (j : xε ≅ yε),
        (iₓ ≫ j.hom.val = f.hom.val ≫ iᵧ) →
          ∀ a, (φ a).val.asIso.hom.val = j.inv.val ≫ a.val.asIso.hom.val ≫ j.hom.val := by
  obtain ⟨f₀, _, hf₀⟩ := existsUnique_pointIso hp x₀ y₀
  obtain ⟨j₀, hj₀, hj₀_unique⟩ :=
    existsUnique_pushforwardIso hp.cofibered g f₀ iₓ hiₓ iᵧ hiᵧ
  obtain ⟨φ₀, hφ₀, hφ₀_unique⟩ :=
    existsUnique_infinitesimalAutomorphismsEquiv
      hp.cofibered g e hpair f₀ iₓ hiₓ iᵧ hiᵧ
  have hφ₀j₀ : ∀ a, (φ₀ a).val.asIso.hom.val = j₀.inv.val ≫ a.val.asIso.hom.val ≫ j₀.hom.val := by
    rcases hφ₀ with ⟨jφ, hjφ, hact⟩
    have hjφ_eq : jφ = j₀ := hj₀_unique jφ hjφ
    subst jφ
    exact fun a => (congrArg (fun x => x.asIso.hom.val) (hact a)).trans (conjAut_hom_val _ _)
  refine ⟨φ₀, ?_, ?_⟩
  · intro f j hcompat a
    obtain rfl := hf₀ f trivial
    obtain rfl := hj₀_unique j hcompat
    exact hφ₀j₀ a
  · intro φ hφ
    apply hφ₀_unique φ
    refine ⟨j₀, hj₀, ?_⟩
    intro a
    exact Aut.ext (Iso.ext (Functor.Fiber.hom_ext ((hφ f₀ j₀ hj₀ a).trans (conjAut_hom_val _ _).symm)))

/-- The canonical identification of infinitesimal automorphism groups attached to
two points, for chosen pushforwards into a common dual-number fibre. -/
public noncomputable def canonicalInfinitesimalAutomorphismsEquiv
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type u₁} [Category.{v₁} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (hp : IsPredeformationCategory p)
    {Aε : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (g : residueFieldObject.{u, v, w} Λ k ⟶ Aε)
    (e : Aε ⟶ residueFieldObject.{u, v, w} Λ k)
    (hpair : IsCanonicalDualNumberPair g e)
    (x₀ y₀ : p.Fiber (residueFieldObject.{u, v, w} Λ k))
    (xε yε : p.Fiber Aε)
    (iₓ : x₀.1 ⟶ xε.1) (hiₓ : p.IsHomLift g iₓ)
    (iᵧ : y₀.1 ⟶ yε.1) (hiᵧ : p.IsHomLift g iᵧ) :
    ↥(infinitesimalAutomorphisms hp.cofibered g e hpair iₓ hiₓ) ≃*
      ↥(infinitesimalAutomorphisms hp.cofibered g e hpair iᵧ hiᵧ) :=
  Classical.choose
    (existsUnique_infinitesimalAutomorphismsEquiv_of_isPredeformationCategory hp g e hpair x₀ y₀ xε
      yε
      iₓ hiₓ iᵧ hiᵧ)

/-- The canonical identification acts by conjugation under every compatible
isomorphism of pushforwards. -/
public theorem canonicalInfinitesimalAutomorphismsEquiv_apply
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type u₁} [Category.{v₁} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (hp : IsPredeformationCategory p)
    {Aε : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (g : residueFieldObject.{u, v, w} Λ k ⟶ Aε)
    (e : Aε ⟶ residueFieldObject.{u, v, w} Λ k)
    (hpair : IsCanonicalDualNumberPair g e)
    (x₀ y₀ : p.Fiber (residueFieldObject.{u, v, w} Λ k))
    (xε yε : p.Fiber Aε)
    (iₓ : x₀.1 ⟶ xε.1) (hiₓ : p.IsHomLift g iₓ)
    (iᵧ : y₀.1 ⟶ yε.1) (hiᵧ : p.IsHomLift g iᵧ)
    (f : x₀ ≅ y₀) (j : xε ≅ yε)
    (hcompat : iₓ ≫ j.hom.val = f.hom.val ≫ iᵧ)
    (a : ↥(infinitesimalAutomorphisms hp.cofibered g e hpair iₓ hiₓ)) :
    ((canonicalInfinitesimalAutomorphismsEquiv hp g e hpair x₀ y₀ xε yε
      iₓ hiₓ iᵧ hiᵧ) a).val.asIso.hom.val =
        j.inv.val ≫ a.val.asIso.hom.val ≫ j.hom.val :=
  (existsUnique_infinitesimalAutomorphismsEquiv_of_isPredeformationCategory
    hp g e hpair x₀ y₀ xε yε iₓ hiₓ iᵧ hiᵧ).choose_spec.1 f j hcompat a

end

/-! ### Infinitesimal automorphisms of a predeformation category -/

section
open CategoryTheory
universe u v w u₁ v₁

/-- The infinitesimal automorphism group of a predeformation category, formed using a
chosen object over the residue field and its pushforward to the dual numbers. -/
@[stacks 06JS "infinitesimal_automorphisms_of_predeformation_category"]
public noncomputable abbrev infinitesimalAutomorphismGroup
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type u₁} [Category.{v₁} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (hp : IsPredeformationCategory p)
    {Aε : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    {x₀ : p.Fiber (residueFieldObject Λ k)} {xε : p.Fiber Aε}
    (g : residueFieldObject Λ k ⟶ Aε)
    (e : Aε ⟶ residueFieldObject Λ k)
    (hpair : IsCanonicalDualNumberPair g e)
    (i : x₀.1 ⟶ xε.1) (hi : p.IsHomLift g i) : Type _ :=
  ↥(infinitesimalAutomorphisms hp.cofibered g e hpair i hi)

/-- Changing the chosen object over the residue field, and its pushforward, gives a unique
identification of infinitesimal automorphism groups. On automorphisms it is conjugation by
the isomorphism between the pushforwards. -/
@[stacks 06JS "infinitesimal_automorphisms_of_predeformation_category"]
public theorem infinitesimalAutomorphismGroup_uniqueEquiv
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type u₁} [Category.{v₁} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (hp : IsPredeformationCategory p)
    {Aε : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    {x₀ y₀ : p.Fiber (residueFieldObject Λ k)}
    {xε yε : p.Fiber Aε}
    (g : residueFieldObject Λ k ⟶ Aε)
    (e : Aε ⟶ residueFieldObject Λ k)
    (hpair : IsCanonicalDualNumberPair g e)
    (i : x₀.1 ⟶ xε.1) (hi : p.IsHomLift g i)
    (j : y₀.1 ⟶ yε.1) (hj : p.IsHomLift g j) :
    ∃! E : infinitesimalAutomorphismGroup hp g e hpair i hi ≃*
        infinitesimalAutomorphismGroup hp g e hpair j hj,
      ∃ (f₀ : x₀ ≅ y₀) (fε : xε ≅ yε),
        f₀.hom.val ≫ j = i ≫ fε.hom.val ∧
        (∀ a, (E a).val = fε.conjAut a.val) := by
  obtain ⟨f₀, -, hf₀⟩ := existsUnique_pointIso hp x₀ y₀
  obtain ⟨E, ⟨fε, hfac, hconj⟩, hE⟩ :=
    existsUnique_infinitesimalAutomorphismsEquiv hp.cofibered g e hpair f₀ i hi j hj
  refine ⟨E, ⟨f₀, fε, hfac.symm, hconj⟩, ?_⟩
  rintro E' ⟨f₀', fε', hfac', hconj'⟩
  have : f₀' = f₀ := hf₀ f₀' trivial
  subst f₀'
  exact hE E' ⟨fε', hfac'.symm, hconj'⟩

end

end Deformation
