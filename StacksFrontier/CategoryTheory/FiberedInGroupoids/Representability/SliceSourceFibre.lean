module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.DiagonalFibre
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFunctoriality

/-!
# The fibre of a 1-morphism out of a slice at a point

Let `p : 𝒳 ⥤ 𝒞` be fibred in groupoids, let `P` be an object of `𝒞` and let `g : 𝒞/P ⥤ 𝒳` be a
1-morphism over `𝒞` out of the slice category. For a category `𝒯` over `𝒞` and a 1-morphism
`y : 𝒯 ⥤ 𝒳` over `𝒞`, this file identifies the first projection of the 2-fibre product
`𝒯 ×_{y, 𝒳, g} 𝒞/P ⟶ 𝒯` with the category of elements of the presheaf on `𝒯` whose sections over
`a` are the pairs `(k, m)` of a morphism `k : p𝒯 a ⟶ P` and a vertical morphism `m : y a ⟶ g k`.

## Main definitions

* `CategoryTheory.TwoFibreProductOver.SliceSourceFibre.SliceHom`: the sections.
* `CategoryTheory.TwoFibreProductOver.SliceSourceFibre.presheaf`: the presheaf.
* `CategoryTheory.TwoFibreProductOver.SliceSourceFibre.ofElements`: the comparison functor from
  its category of elements to the 2-fibre product.

## Main results

* `CategoryTheory.TwoFibreProductOver.SliceSourceFibre.nonempty_equivalenceOver`: the first
  projection of the 2-fibre product is equivalent over `𝒯` to the category of elements.
-/

@[expose] public section

open CategoryTheory Functor

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.TwoFibreProductOver.SliceSourceFibre

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {X : Type u₃} [Category.{v₃} X]
  {𝒯 : Type u₂} [Category.{v₂} 𝒯]

/-- A section over `a` of the fibre presheaf: a morphism `k : p𝒯 a ⟶ P` together with a vertical
morphism `y a ⟶ g k`. -/
structure SliceHom (p : X ⥤ 𝒞) (p𝒯 : 𝒯 ⥤ 𝒞) (P : 𝒞) (y : 𝒯 ⥤ X) (g : Over P ⥤ X) (a : 𝒯) where
  /-- The morphism to `P`. -/
  k : p𝒯.obj a ⟶ P
  /-- The vertical morphism. -/
  m : y.obj a ⟶ g.obj (Over.mk k)
  /-- Verticality. -/
  vert : p.IsHomLift (𝟙 (p𝒯.obj a)) m

namespace SliceHom

variable {p : X ⥤ 𝒞} {p𝒯 : 𝒯 ⥤ 𝒞} {P : 𝒞} {y : 𝒯 ⥤ X} {g : Over P ⥤ X}

attribute [instance] SliceHom.vert

/-- Two sections agree when their morphisms to `P` agree and their vertical morphisms agree up to
the transport along that equality. -/
lemma ext' {a : 𝒯} {s t : SliceHom p p𝒯 P y g a} (hk : s.k = t.k)
    (hm : s.m ≫ g.map (eqToHom (by rw [hk])) = t.m) : s = t := by
  obtain ⟨k, m, _⟩ := s
  obtain ⟨k', m', _⟩ := t
  dsimp only at hk hm
  subst hk
  simp only [eqToHom_refl, Functor.map_id, Category.comp_id] at hm
  subst hm
  rfl

/-- The image under `g` of a morphism `u` of `Over P` lies over `u.left`. -/
lemma isHomLift_g_map (hg : g ⋙ p = Over.forget P) {b b' : Over P} (u : b ⟶ b') :
    p.IsHomLift u.left (g.map u) := by
  refine IsHomLift.of_fac' p _ _ (Functor.congr_obj hg b) (Functor.congr_obj hg b') ?_
  have := Functor.congr_hom hg u
  simp only [Functor.comp_map] at this
  rw [this]
  rfl

/-- The image under `y` of a morphism `h` of `𝒯` lies over `p𝒯.map h`. -/
lemma isHomLift_y_map (hy : y ⋙ p = p𝒯) {a' a : 𝒯} (h : a' ⟶ a) :
    p.IsHomLift (p𝒯.map h) (y.map h) := by
  refine IsHomLift.of_fac' p _ _ (Functor.congr_obj hy a') (Functor.congr_obj hy a) ?_
  have := Functor.congr_hom hy h
  simp only [Functor.comp_map] at this
  rw [this]

/-- The composite `y.map h ≫ s.m` lies over `p𝒯.map h`. -/
lemma isHomLift_comp (hy : y ⋙ p = p𝒯) {a' a : 𝒯} (h : a' ⟶ a) (s : SliceHom p p𝒯 P y g a) :
    p.IsHomLift (p𝒯.map h) (y.map h ≫ s.m) := by
  have h1 : p.IsHomLift (p𝒯.map h) (y.map h) := isHomLift_y_map hy h
  have : p.IsHomLift (p𝒯.map h ≫ 𝟙 (p𝒯.obj a)) (y.map h ≫ s.m) := inferInstance
  rwa [Category.comp_id] at this

variable (hp : p.IsFiberedInGroupoids) (hy : y ⋙ p = p𝒯) (hg : g ⋙ p = Over.forget P)
include hp hy hg

/-- Restriction of a section along `h : a' ⟶ a`: precompose the morphism to `P` with `p𝒯 h`, and
fill in the vertical morphism against the cartesian morphism lying over `p𝒯 h`. -/
noncomputable def restrict {a' a : 𝒯} (h : a' ⟶ a) (s : SliceHom p p𝒯 P y g a) :
    SliceHom p p𝒯 P y g a' :=
  have : p.IsHomLift (p𝒯.map h)
      (g.map (Over.homMk (p𝒯.map h) rfl : Over.mk (p𝒯.map h ≫ s.k) ⟶ Over.mk s.k)) :=
    isHomLift_g_map hg (Over.homMk (p𝒯.map h) rfl : Over.mk (p𝒯.map h ≫ s.k) ⟶ Over.mk s.k)
  have := isHomLift_comp hy h s
  have _hsc : p.IsStronglyCartesian (p𝒯.map h)
      (g.map (Over.homMk (p𝒯.map h) rfl : Over.mk (p𝒯.map h ≫ s.k) ⟶ Over.mk s.k)) :=
    hp.isStronglyCartesian_homLift _ _
  { k := p𝒯.map h ≫ s.k
    m := Functor.IsStronglyCartesian.map p (p𝒯.map h)
      (g.map (Over.homMk (p𝒯.map h) rfl : Over.mk (p𝒯.map h ≫ s.k) ⟶ Over.mk s.k))
      (Category.id_comp _).symm (y.map h ≫ s.m)
    vert := inferInstance }

/-- The morphism to `P` of the restriction of `s` along `h` is `p𝒯.map h ≫ s.k`. -/
@[simp] lemma restrict_k {a' a : 𝒯} (h : a' ⟶ a) (s : SliceHom p p𝒯 P y g a) :
    (restrict hp hy hg h s).k = p𝒯.map h ≫ s.k := rfl

/-- The vertical morphism of the restriction of `s` along `h`, followed by the image under `g` of
the morphism `p𝒯.map h` of `Over P`, is `y.map h ≫ s.m`. -/
lemma restrict_fac {a' a : 𝒯} (h : a' ⟶ a) (s : SliceHom p p𝒯 P y g a) :
    (restrict hp hy hg h s).m ≫
        g.map (Over.homMk (p𝒯.map h) (by simp) : Over.mk (restrict hp hy hg h s).k ⟶ Over.mk s.k) =
      y.map h ≫ s.m := by
  have : p.IsHomLift (p𝒯.map h)
      (g.map (Over.homMk (p𝒯.map h) rfl : Over.mk (p𝒯.map h ≫ s.k) ⟶ Over.mk s.k)) :=
    isHomLift_g_map hg (Over.homMk (p𝒯.map h) rfl : Over.mk (p𝒯.map h ≫ s.k) ⟶ Over.mk s.k)
  have := isHomLift_comp hy h s
  have _hsc : p.IsStronglyCartesian (p𝒯.map h)
      (g.map (Over.homMk (p𝒯.map h) rfl : Over.mk (p𝒯.map h ≫ s.k) ⟶ Over.mk s.k)) :=
    hp.isStronglyCartesian_homLift _ _
  exact Functor.IsStronglyCartesian.fac p (p𝒯.map h)
    (g.map (Over.homMk (p𝒯.map h) rfl : Over.mk (p𝒯.map h ≫ s.k) ⟶ Over.mk s.k))
    (Category.id_comp _).symm (y.map h ≫ s.m)

/-- The restriction is characterized by its morphism to `P` and its factorization. -/
lemma eq_restrict {a' a : 𝒯} (h : a' ⟶ a) (s : SliceHom p p𝒯 P y g a)
    (t : SliceHom p p𝒯 P y g a') (hk : t.k = p𝒯.map h ≫ s.k)
    (hm : t.m ≫ g.map (Over.homMk (p𝒯.map h) (by simp [hk]) : Over.mk t.k ⟶ Over.mk s.k) =
      y.map h ≫ s.m) :
    t = restrict hp hy hg h s := by
  obtain ⟨k, m, hv⟩ := t
  dsimp only at hk hm
  subst hk
  have : p.IsHomLift (p𝒯.map h)
      (g.map (Over.homMk (p𝒯.map h) rfl : Over.mk (p𝒯.map h ≫ s.k) ⟶ Over.mk s.k)) :=
    isHomLift_g_map hg (Over.homMk (p𝒯.map h) rfl : Over.mk (p𝒯.map h ≫ s.k) ⟶ Over.mk s.k)
  have := isHomLift_comp hy h s
  have _hsc : p.IsStronglyCartesian (p𝒯.map h)
      (g.map (Over.homMk (p𝒯.map h) rfl : Over.mk (p𝒯.map h ≫ s.k) ⟶ Over.mk s.k)) :=
    hp.isStronglyCartesian_homLift _ _
  have key := Functor.IsStronglyCartesian.map_uniq p (p𝒯.map h)
    (g.map (Over.homMk (p𝒯.map h) rfl : Over.mk (p𝒯.map h ≫ s.k) ⟶ Over.mk s.k))
    (Category.id_comp _).symm (y.map h ≫ s.m) m hm
  subst key
  rfl

/-- Restriction along the identity is the identity. -/
lemma restrict_id {a : 𝒯} (s : SliceHom p p𝒯 P y g a) : restrict hp hy hg (𝟙 a) s = s := by
  refine (eq_restrict hp hy hg (𝟙 a) s s (by simp) ?_).symm
  have : (Over.homMk (p𝒯.map (𝟙 a)) (by simp) : Over.mk s.k ⟶ Over.mk s.k) = 𝟙 _ := by
    ext; simp
  rw [this, Functor.map_id, Functor.map_id, Category.comp_id, Category.id_comp]

/-- Restriction along `f ≫ h` is restriction along `h` followed by restriction along `f`. -/
lemma restrict_comp {a'' a' a : 𝒯} (f : a'' ⟶ a') (h : a' ⟶ a) (s : SliceHom p p𝒯 P y g a) :
    restrict hp hy hg (f ≫ h) s = restrict hp hy hg f (restrict hp hy hg h s) := by
  refine (eq_restrict hp hy hg (f ≫ h) s _ (by simp) ?_).symm
  have hfac := restrict_fac hp hy hg f (restrict hp hy hg h s)
  have hfac' := restrict_fac hp hy hg h s
  have hsplit : (Over.homMk (p𝒯.map (f ≫ h)) (by simp) :
      Over.mk (restrict hp hy hg f (restrict hp hy hg h s)).k ⟶ Over.mk s.k) =
      (Over.homMk (p𝒯.map f) (by simp) : Over.mk (restrict hp hy hg f
          (restrict hp hy hg h s)).k ⟶ Over.mk (restrict hp hy hg h s).k) ≫
        (Over.homMk (p𝒯.map h) (by simp) :
          Over.mk (restrict hp hy hg h s).k ⟶ Over.mk s.k) := by
    ext
    simp
  rw [hsplit, Functor.map_comp, ← Category.assoc, hfac, Category.assoc, hfac', Functor.map_comp,
    Category.assoc]

omit hy hg in
/-- The vertical morphism of a section is an isomorphism. -/
lemma isIso_m {a : 𝒯} (s : SliceHom p p𝒯 P y g a) : IsIso s.m := by
  have := hp.isStronglyCartesian_homLift (𝟙 (p𝒯.obj a)) s.m
  exact Functor.IsStronglyCartesian.isIso_of_base_isIso p (𝟙 (p𝒯.obj a)) s.m

/-- If `s` is the restriction of `t` along `h`, then `s.k = p𝒯.map h ≫ t.k`. -/
lemma k_eq_of_eq_restrict {a' a : 𝒯} {h : a' ⟶ a} {s : SliceHom p p𝒯 P y g a'}
    {t : SliceHom p p𝒯 P y g a} (e : s = restrict hp hy hg h t) : s.k = p𝒯.map h ≫ t.k := by
  subst e; rfl

/-- If `s` is the restriction of `t` along `h`, then `y.map h ≫ t.m` equals `s.m` followed by the
image under `g` of the morphism `p𝒯.map h` of `Over P`. -/
lemma w_of_eq_restrict {a' a : 𝒯} {h : a' ⟶ a} {s : SliceHom p p𝒯 P y g a'}
    {t : SliceHom p p𝒯 P y g a} (e : s = restrict hp hy hg h t) :
    y.map h ≫ t.m = s.m ≫ g.map (Over.homMk (p𝒯.map h)
      (by simp [k_eq_of_eq_restrict hp hy hg e]) : Over.mk s.k ⟶ Over.mk t.k) := by
  subst e
  exact (restrict_fac hp hy hg h t).symm

end SliceHom

open SliceHom

variable {p : X ⥤ 𝒞} {p𝒯 : 𝒯 ⥤ 𝒞} {P : 𝒞} {y : 𝒯 ⥤ X} {g : Over P ⥤ X}
  (hp : p.IsFiberedInGroupoids) (hy : y ⋙ p = p𝒯) (hg : g ⋙ p = Over.forget P)

/-- The presheaf on `𝒯` of pairs `(k, m)` of a morphism `k : p𝒯 a ⟶ P` and a vertical morphism
`m : y a ⟶ g k`, with restriction maps `SliceHom.restrict`. -/
noncomputable abbrev presheaf : 𝒯ᵒᵖ ⥤ Type (max v₁ v₃) where
  obj a := SliceHom p p𝒯 P y g a.unop
  map h := ↾fun s => restrict hp hy hg h.unop s
  map_id _ := by
    ext s
    exact restrict_id hp hy hg s
  map_comp f h := by
    ext s
    exact restrict_comp hp hy hg h.unop f.unop s

/-- The restriction maps of `presheaf` are given by `SliceHom.restrict`. -/
@[simp] lemma presheaf_map {a' a : 𝒯} (h : a' ⟶ a) (s : SliceHom p p𝒯 P y g a) :
    (presheaf hp hy hg).map h.op s = restrict hp hy hg h s := rfl

/-- The comparison functor from the category of elements of the fibre presheaf to the 2-fibre
product: a section `(k, m)` over `a` goes to `(a, k, m)`. -/
noncomputable abbrev ofElements :
    (presheafOfCategories (presheaf hp hy hg ⋙ typeToCat)).obj ⥤
      TwoFibreProductOver p𝒯 (Over.forget P) p y g where
  obj Z :=
    have := isIso_m hp Z.fiber.as
    { base := p𝒯.obj Z.base
      x := Z.base
      y := Over.mk Z.fiber.as.k
      hx := rfl
      hy := rfl
      iso := asIso Z.fiber.as.m
      vertical := Z.fiber.as.vert }
  map {Z W} u :=
    have hfib : Z.fiber.as = restrict hp hy hg u.base W.fiber.as := Discrete.eq_of_hom u.fiber
    { hbase := p𝒯.map u.base
      a := u.base
      b := Over.homMk (p𝒯.map u.base) (by simp [k_eq_of_eq_restrict hp hy hg hfib])
      ha := IsHomLift.map p𝒯 u.base
      hb := IsHomLift.map (Over.forget P) (Over.homMk (p𝒯.map u.base)
        (by simp [k_eq_of_eq_restrict hp hy hg hfib]) :
          Over.mk Z.fiber.as.k ⟶ Over.mk W.fiber.as.k)
      w := w_of_eq_restrict hp hy hg hfib }
  map_id Z := Hom.ext' rfl (Over.OverMorphism.ext (p𝒯.map_id Z.base))
  map_comp u v := Hom.ext' rfl (Over.OverMorphism.ext (p𝒯.map_comp u.base v.base))

/-- The comparison functor `ofElements` is faithful. -/
instance : (ofElements hp hy hg).Faithful where
  map_injective {Z W} u v huv :=
    PresheafOfCategories.elements_hom_ext u v (by simpa [ofElements] using congrArg Hom.a huv)

/-- The comparison functor `ofElements` is full. -/
instance : (ofElements hp hy hg).Full where
  map_surjective {Z W} v := by
    have ha := v.ha
    have hb := v.hb
    have hha : p𝒯.map v.a = v.hbase := by
      have h := IsHomLift.fac' p𝒯 v.hbase v.a
      simpa using h
    have hhb : v.b.left = v.hbase := by
      have h := IsHomLift.fac' (Over.forget P) v.hbase v.b
      simpa using h
    have hbl : v.b.left = p𝒯.map v.a := hhb.trans hha.symm
    have hk : Z.fiber.as.k = p𝒯.map v.a ≫ W.fiber.as.k := by
      have := Over.w v.b
      rw [← hbl]
      simpa using this.symm
    have hbv : v.b = (Over.homMk (p𝒯.map v.a) (by simp [hk]) :
        Over.mk Z.fiber.as.k ⟶ Over.mk W.fiber.as.k) :=
      Over.OverMorphism.ext hbl
    have hfib : Z.fiber.as = restrict hp hy hg v.a W.fiber.as := by
      refine eq_restrict hp hy hg v.a W.fiber.as Z.fiber.as hk ?_
      have := v.w
      rw [hbv] at this
      exact this.symm
    refine ⟨⟨v.a, Discrete.eqToHom hfib⟩, ?_⟩
    refine Hom.ext' rfl ?_
    exact Over.OverMorphism.ext hbl.symm

/-- The comparison functor `ofElements` is essentially surjective. -/
instance : (ofElements hp hy hg).EssSurj where
  mem_essImage A := by
    let k : p𝒯.obj A.x ⟶ P := eqToHom (A.hx.trans A.hy.symm) ≫ A.y.hom
    let ι : A.y ≅ Over.mk k := Over.isoMk (eqToIso (A.hy.trans A.hx.symm)) (by simp [k])
    have hv : p.IsHomLift (𝟙 (p𝒯.obj A.x)) (A.iso.hom ≫ g.map ι.hom) := by
      have h1 := A.vertical
      have h2 : p.IsHomLift ι.hom.left (g.map ι.hom) := isHomLift_g_map hg ι.hom
      refine IsHomLift.of_fac' p _ _ (Functor.congr_obj hy A.x) ?_ ?_
      · exact Functor.congr_obj hg (Over.mk k)
      · rw [Functor.map_comp, IsHomLift.fac' p (𝟙 A.base) A.iso.hom,
          IsHomLift.fac' p ι.hom.left (g.map ι.hom)]
        simp [ι]
    let s : SliceHom p p𝒯 P y g A.x := ⟨k, A.iso.hom ≫ g.map ι.hom, hv⟩
    have := isIso_m hp s
    refine ⟨⟨A.x, ⟨s⟩⟩, ⟨?_⟩⟩
    exact
      { hom :=
          { hbase := eqToHom A.hx
            a := 𝟙 A.x
            b := ι.inv
            ha := IsHomLift.of_fac' p𝒯 _ _ rfl A.hx (by simp)
            hb := IsHomLift.of_fac' (Over.forget P) _ _ rfl A.hy (by simp [ι])
            w := by
              change y.map (𝟙 A.x) ≫ A.iso.hom = (A.iso.hom ≫ g.map ι.hom) ≫ g.map ι.inv
              simp [← Functor.map_comp] }
        inv :=
          { hbase := eqToHom A.hx.symm
            a := 𝟙 A.x
            b := ι.hom
            ha := IsHomLift.of_fac' p𝒯 _ _ A.hx rfl (by simp)
            hb := IsHomLift.of_fac' (Over.forget P) _ _ A.hy rfl (by simp [ι])
            w := by
              change y.map (𝟙 A.x) ≫ (A.iso.hom ≫ g.map ι.hom) = A.iso.hom ≫ g.map ι.hom
              simp }
        hom_inv_id := Hom.ext' (by simp) (by simp)
        inv_hom_id := Hom.ext' (by simp) (by simp) }

end CategoryTheory.TwoFibreProductOver.SliceSourceFibre

namespace CategoryTheory.TwoFibreProductOver.SliceSourceFibre

universe v

variable {𝒞 : Type u₁} [Category.{v} 𝒞] {X : Type u₃} [Category.{v} X]
  {𝒯 : Type u₂} [Category.{v} 𝒯]
  {p : X ⥤ 𝒞} {p𝒯 : 𝒯 ⥤ 𝒞} {P : 𝒞} {y : 𝒯 ⥤ X} {g : Over P ⥤ X}

/-- **The fibre of a 1-morphism out of a slice at a point.** The first projection of
`𝒯 ×_{y, 𝒳, g} 𝒞/P` is equivalent over `𝒯` to the category of elements of the presheaf of pairs
`(k, m)` of a morphism `k : p𝒯 a ⟶ P` and a vertical morphism `m : y a ⟶ g k`. -/
theorem nonempty_equivalenceOver (hp : p.IsFiberedInGroupoids) (hy : y ⋙ p = p𝒯)
    (hg : g ⋙ p = Over.forget P)
    (hfst : (fst p𝒯 (Over.forget P) p y g).IsFiberedInGroupoids) :
    Nonempty (StacksRepresentableCFG.EquivalenceOver (fst p𝒯 (Over.forget P) p y g)
      (presheafOfCategories (presheaf hp hy hg ⋙ typeToCat)).p) :=
  ⟨(StacksRepresentableCFG.equivalenceOverOfIsEquivalence
    (PresheafOfCategories.isFiberedInSetoids_discreteProjection _).isFiberedInGroupoids hfst
    (ofElements hp hy hg) rfl { }).symm⟩

end CategoryTheory.TwoFibreProductOver.SliceSourceFibre

end
