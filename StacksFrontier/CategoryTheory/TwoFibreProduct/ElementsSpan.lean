module

public import StacksFrontier.CategoryTheory.FiberedCategory.ElementsSection
public import StacksFrontier.CategoryTheory.FiberedCategory.Inertia
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Transport
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverIso

/-!
# Sections of a presheaf representing a 2-fibre product

Let `p𝒳 : 𝒳 ⥤ 𝒞`, `p𝒴 : 𝒴 ⥤ 𝒞` and `p𝒮 : 𝒮 ⥤ 𝒞` be categories over `𝒞`, let `F : 𝒳 ⥤ 𝒮` be
strictly over `𝒞` and let `G` be a 1-morphism over `𝒞` from `p𝒴` to `p𝒮`. Suppose the first
projection of the 2-fibre product `𝒳 ×_𝒮 𝒴` is equivalent over `𝒳` to the category of elements
of a presheaf `P` on `𝒳` — that is, that projection is *represented* by `P`. Then every object of
the 2-fibre product names a section of `P` (`CategoryTheory.PresheafOfCategories.sectionOfObj`),
and the question of which sections exist becomes a question about the 2-fibre product.

Given a commuting square

```text
  W --j--> V
  |        |
  k        a
  v        v
 A.x --t-> T
```

in `𝒳`, an object `A` of the 2-fibre product, and a span

```text
  z_W --m--> z_V
   |
   n
   v
  A.y
```

in `𝒴` whose legs lie over `p𝒳 k` and `p𝒳 j`, compatible with a morphism
`b : G(z_V) ⟶ F(T)` over `p𝒳 a` in the sense that `G(n)` followed by the comparison isomorphism
of `A` and `F(t)` agrees with `G(m)` followed by `b`, there is a section of `P` over `V` whose
restriction along `j` is the restriction along `k` of the section named by `A`.

## Main results

* `CategoryTheory.TwoFibreProductOver.isHomLift_b_of_isHomLift_fst`: the `𝒴`-component of a
  morphism of the 2-fibre product lying over `r` for the first projection lies over `p𝒳 r`.
* `CategoryTheory.TwoFibreProductOver.exists_mk_of_section`: every section of `P` over an object
  of `𝒳` is named by an object of the 2-fibre product with that object as its `𝒳`-component.
* `CategoryTheory.TwoFibreProductOver.exists_section_of_span`: the existence statement described
  above, for `p𝒮` fibred in groupoids.

## References

* [Stacks Project, Tag 02XV](https://stacks.math.columbia.edu/tag/02XV)
* [Stacks Project, Tag 04SD](https://stacks.math.columbia.edu/tag/04SD)
-/

@[expose] public section

open CategoryTheory Opposite

namespace CategoryTheory.TwoFibreProductOver

universe v₁ v₂ v₃ v₄ a u₁ u₂ u₃ u₄

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {𝒴 : Type u₃} [Category.{v₃} 𝒴] {𝒮 : Type u₄} [Category.{v₄} 𝒮]
  {p𝒳 : 𝒳 ⥤ 𝒞} {p𝒴 : 𝒴 ⥤ 𝒞} {p𝒮 : 𝒮 ⥤ 𝒞} {F : 𝒳 ⥤ 𝒮} {G : 𝒴 ⥤ 𝒮}

/-- A morphism of the 2-fibre product lying over `r : U ⟶ V` of `𝒳` for the *first projection*
has its `𝒴`-component lying over `p𝒳 r` for `p𝒴`. -/
theorem isHomLift_b_of_isHomLift_fst {Q Q' : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G} {U V : 𝒳}
    (r : U ⟶ V) (φ : Q ⟶ Q') (hφ : (fst p𝒳 p𝒴 p𝒮 F G).IsHomLift r φ) :
    p𝒴.IsHomLift (p𝒳.map r) φ.b :=
  isHomLift_b φ (p𝒳.map r)
    (Functor.isHomLift_base_of_comp_eq _ p𝒳 (fst p𝒳 p𝒴 p𝒮 F G) fst_comp_eq r φ hφ)

section Sections

variable {P : 𝒳ᵒᵖ ⥤ Type a}
  (e : StacksRepresentableCFG.EquivalenceOver (fst p𝒳 p𝒴 p𝒮 F G)
    (presheafOfCategories (P ⋙ typeToCat)).p)

/-- Every section of `P` over `V` is named by an object of the 2-fibre product whose
`𝒳`-component is `V` itself. -/
theorem exists_mk_of_section (V : 𝒳) (s : P.obj (op V)) :
    ∃ (w : 𝒴) (hw : p𝒴.obj w = p𝒳.obj V) (i : F.obj V ≅ G.obj w)
      (hi : p𝒮.IsHomLift (𝟙 (p𝒳.obj V)) i.hom),
      PresheafOfCategories.sectionOfObj e ⟨p𝒳.obj V, V, w, rfl, hw, i, hi⟩ rfl = s := by
  obtain ⟨A, hA, hs⟩ := PresheafOfCategories.exists_sectionOfObj e s
  obtain ⟨Abase, Ax, Ay, Ahx, Ahy, Aiso, Avert⟩ := A
  change Ax = V at hA
  subst hA
  subst Ahx
  exact ⟨Ay, Ahy, Aiso, Avert, hs⟩

/-- A span in `𝒴` over a commuting square in `𝒳`, compatible with a morphism of `𝒮` over the
remaining edge, produces a section of `P` whose restriction along one edge of the square is the
restriction along the other of the section named by `A`. -/
theorem exists_section_of_span (hp𝒮 : p𝒮.IsFiberedInGroupoids) (hF : F ⋙ p𝒮 = p𝒳)
    (hG : G ⋙ p𝒮 = p𝒴) (A : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G)
    {T V W : 𝒳} (t : A.x ⟶ T) (a : V ⟶ T) (k : W ⟶ A.x) (j : W ⟶ V)
    (hsq : j ≫ a = k ≫ t) {zW zV : 𝒴} (n : zW ⟶ A.y) (m : zW ⟶ zV)
    (b : G.obj zV ⟶ F.obj T)
    (hn : p𝒴.IsHomLift (p𝒳.map k) n) (hm : p𝒴.IsHomLift (p𝒳.map j) m)
    (hb : p𝒮.IsHomLift (p𝒳.map a) b)
    (h : G.map n ≫ A.iso.inv ≫ F.map t = G.map m ≫ b) :
    ∃ z : P.obj (op V),
      P.map j.op z = P.map k.op (PresheafOfCategories.sectionOfObj e A rfl) := by
  have hFlift : ∀ {V' W' : 𝒳} (r : V' ⟶ W'), p𝒮.IsHomLift (p𝒳.map r) (F.map r) := by
    intro V' W' r
    have := IsHomLift.map (p := p𝒳) r
    exact Functor.isHomLift_map_of_comp_eq hF (p𝒳.map r) r
  have hGn : p𝒮.IsHomLift (p𝒳.map k) (G.map n) :=
    have := hn
    Functor.isHomLift_map_of_comp_eq hG (p𝒳.map k) n
  have hGm : p𝒮.IsHomLift (p𝒳.map j) (G.map m) :=
    have := hm
    Functor.isHomLift_map_of_comp_eq hG (p𝒳.map j) m
  have hiso : p𝒮.IsHomLift (𝟙 (p𝒳.obj A.x)) A.iso.hom := A.hx ▸ A.vertical
  have hka : p𝒮.IsHomLift (p𝒳.map k) (F.map k ≫ A.iso.hom) :=
    have := hFlift k
    IsHomLift.comp_lift_id_right _ _ _ _
  have hcartb := hp𝒮.isStronglyCartesian_homLift (p𝒳.map a) b
  have hcartn := hp𝒮.isStronglyCartesian_homLift (p𝒳.map k) (G.map n)
  have hFa := hFlift a
  have hFt := hFlift t
  have hβ := Functor.IsStronglyCartesian.map_isHomLift p𝒮 (p𝒳.map a) b
    (Category.id_comp (p𝒳.map a)).symm (F.map a)
  have hθ := Functor.IsStronglyCartesian.map_isHomLift p𝒮 (p𝒳.map k) (G.map n)
    (Category.id_comp (p𝒳.map k)).symm (F.map k ≫ A.iso.hom)
  set β := Functor.IsStronglyCartesian.map p𝒮 (p𝒳.map a) b
    (Category.id_comp (p𝒳.map a)).symm (F.map a) with hβdef
  set θ := Functor.IsStronglyCartesian.map p𝒮 (p𝒳.map k) (G.map n)
    (Category.id_comp (p𝒳.map k)).symm (F.map k ≫ A.iso.hom) with hθdef
  have hβiso : IsIso β :=
    Functor.isIso_of_fiber_isGroupoid (hp𝒮.fiber_isGroupoid (p𝒳.obj V)) β hβ
  have hθiso : IsIso θ :=
    Functor.isIso_of_fiber_isGroupoid (hp𝒮.fiber_isGroupoid (p𝒳.obj W)) θ hθ
  have hβfac : β ≫ b = F.map a := Functor.IsStronglyCartesian.fac p𝒮 (p𝒳.map a) b
    (Category.id_comp (p𝒳.map a)).symm (F.map a)
  have hθfac : θ ≫ G.map n = F.map k ≫ A.iso.hom :=
    Functor.IsStronglyCartesian.fac p𝒮 (p𝒳.map k) (G.map n)
      (Category.id_comp (p𝒳.map k)).symm (F.map k ≫ A.iso.hom)
  set QV : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G :=
    ⟨p𝒳.obj V, V, zV, rfl, IsHomLift.codomain_eq p𝒴 (p𝒳.map j) m, asIso β, hβ⟩ with hQV
  set QW : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G :=
    ⟨p𝒳.obj W, W, zW, rfl, IsHomLift.domain_eq p𝒴 (p𝒳.map j) m, asIso θ, hθ⟩ with hQW
  have hw : F.map j ≫ β = θ ≫ G.map m := by
    have hl : p𝒮.IsHomLift (p𝒳.map j) (F.map j ≫ β) :=
      have := hFlift j
      IsHomLift.comp_lift_id_right _ _ _ _
    have hr : p𝒮.IsHomLift (p𝒳.map j) (θ ≫ G.map m) :=
      IsHomLift.comp_lift_id_left _ _ _ _
    refine Functor.IsStronglyCartesian.ext p𝒮 (p𝒳.map a) b (p𝒳.map j) ?_
    calc (F.map j ≫ β) ≫ b = F.map j ≫ F.map a := by rw [Category.assoc, hβfac]
      _ = F.map k ≫ F.map t := by rw [← F.map_comp, hsq, F.map_comp]
      _ = θ ≫ G.map n ≫ A.iso.inv ≫ F.map t := by
          rw [← Category.assoc θ (G.map n), hθfac]
          simp only [Category.assoc, Iso.hom_inv_id_assoc]
      _ = (θ ≫ G.map m) ≫ b := by rw [h, Category.assoc]
  let nm : QW ⟶ A :=
    { hbase := p𝒳.map k ≫ eqToHom A.hx
      a := k
      b := n
      ha := (IsHomLift.lift_comp_eqToHom_iff p𝒳 (p𝒳.map k) k A.hx).mpr (IsHomLift.map p𝒳 k)
      hb := (IsHomLift.lift_comp_eqToHom_iff p𝒴 (p𝒳.map k) n A.hx).mpr hn
      w := hθfac.symm }
  let mm : QW ⟶ QV :=
    { hbase := p𝒳.map j
      a := j
      b := m
      ha := IsHomLift.map p𝒳 j
      hb := hm
      w := hw }
  have hlnm : (fst p𝒳 p𝒴 p𝒮 F G).IsHomLift k nm :=
    IsHomLift.of_fac' _ _ _ rfl rfl (by
      show k = eqToHom rfl ≫ k ≫ eqToHom rfl
      simp)
  have hlmm : (fst p𝒳 p𝒴 p𝒮 F G).IsHomLift j mm :=
    IsHomLift.of_fac' _ _ _ rfl rfl (by
      show j = eqToHom rfl ≫ j ≫ eqToHom rfl
      simp)
  refine ⟨PresheafOfCategories.sectionOfObj e QV rfl, ?_⟩
  exact (PresheafOfCategories.sectionOfObj_map e (z := QV) (z' := QW) rfl rfl j mm hlmm).symm.trans
    (PresheafOfCategories.sectionOfObj_map e (z := A) (z' := QW) rfl rfl k nm hlnm)

end Sections

end CategoryTheory.TwoFibreProductOver

end
