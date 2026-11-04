module

public import StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsSheaf.AffineSheaf

/-!
# Extending functors from a full subcategory of schemes: the extension is a Zariski sheaf

This is the fourth part of `StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsSheaf`.
It contains the projections `extensionπ` of the limit computing the extension and the section
`extensionMk` attached to a compatible family, the separatedness of the colimit formula
(`affineExtension_ext`), and the analogue of condition (a) for the extension
(`isZariskiSheaf_extension`).

## References

* [Stacks Project, Tag 0EUW](https://stacks.math.columbia.edu/tag/0EUW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.ExtendingFunctors

universe v w u

variable {S : Scheme.{u}}

section Extension

/-! ### The limit computing the extension -/

variable (P : ObjectProperty (Over S)) (F : P.FullSubcategoryᵒᵖ ⥤ Type (max w (u + 1)))

/-- The diagram whose limit is the value of the extension at `X`: the colimit formula evaluated
at the affine objects over affine opens of `S` mapping to `X`. -/
noncomputable abbrev affineDiagram (X : Over S) :
    StructuredArrow (op X) (IsAffineOverAffineOpen (S := S)).ι.op ⥤ Type (max w (u + 1)) :=
  StructuredArrow.proj (op X) (IsAffineOverAffineOpen (S := S)).ι.op ⋙
    ((IsAffineOverAffineOpen (S := S)).ι.op ⋙ affineExtension P F)

/-- The projection of the limit defining the extension, at an affine object lying over an affine
open of `S` together with a morphism to `X`. -/
noncomputable def extensionπ {X V : Over S} (hV : IsAffineOverAffineOpen V) (f : V ⟶ X) :
    (extension P F).obj (op X) ⟶ (affineExtension P F).obj (op V) :=
  limit.π (affineDiagram P F X) (StructuredArrow.mk
    (Y := op (⟨V, hV⟩ : (IsAffineOverAffineOpen (S := S)).FullSubcategory)) f.op)

/-- The projection at `f` of the restriction of a section along `g` is its projection at
`f ≫ g`. -/
lemma extensionπ_naturality {X X' V : Over S} (g : X' ⟶ X) (hV : IsAffineOverAffineOpen V)
    (f : V ⟶ X') (t : (extension P F).obj (op X)) :
    extensionπ P F hV f ((extension P F).map g.op t) = extensionπ P F hV (f ≫ g) t := by
  have hw : (extension P F).map g.op ≫ extensionπ P F hV f = extensionπ P F hV (f ≫ g) :=
    limit.lift_π _ _
  exact ConcreteCategory.congr_hom hw t

/-- Restricting the projection at `f` along `k` gives the projection at `k ≫ f`. -/
lemma extensionπ_map {X V V' : Over S} (hV : IsAffineOverAffineOpen V)
    (hV' : IsAffineOverAffineOpen V') (k : V' ⟶ V) (f : V ⟶ X)
    (t : (extension P F).obj (op X)) :
    (affineExtension P F).map k.op (extensionπ P F hV f t) = extensionπ P F hV' (k ≫ f) t := by
  let d : StructuredArrow (op X) (IsAffineOverAffineOpen (S := S)).ι.op :=
    StructuredArrow.mk (Y := op (⟨V, hV⟩ : (IsAffineOverAffineOpen (S := S)).FullSubcategory)) f.op
  let d' : StructuredArrow (op X) (IsAffineOverAffineOpen (S := S)).ι.op :=
    StructuredArrow.mk
      (Y := op (⟨V', hV'⟩ : (IsAffineOverAffineOpen (S := S)).FullSubcategory)) (k ≫ f).op
  have hw := limit.w (affineDiagram P F X)
    (StructuredArrow.homMk (f := d) (f' := d') (ObjectProperty.homMk k).op rfl)
  exact ConcreteCategory.congr_hom hw t

/-- Two sections of the extension agree as soon as all their projections agree. -/
lemma extension_ext {X : Over S} (t t' : (extension P F).obj (op X))
    (h : ∀ (V : Over S) (hV : IsAffineOverAffineOpen V) (f : V ⟶ X),
      extensionπ P F hV f t = extensionπ P F hV f t') : t = t' :=
  Types.limit_ext _ t t' fun d => h d.right.unop.obj d.right.unop.property d.hom.unop

/-- A compatible family of sections of the colimit formula is a section of the extension. -/
noncomputable def extensionMk {X : Over S}
    (x : ∀ (V : Over S), IsAffineOverAffineOpen V → (V ⟶ X) →
      (affineExtension P F).obj (op V))
    (h : ∀ (V V' : Over S) (hV : IsAffineOverAffineOpen V) (hV' : IsAffineOverAffineOpen V')
      (f : V ⟶ X) (k : V' ⟶ V),
      (affineExtension P F).map k.op (x V hV f) = x V' hV' (k ≫ f)) :
    (extension P F).obj (op X) := by
  refine Types.Limit.mk (affineDiagram P F X)
    (fun d => x d.right.unop.obj d.right.unop.property d.hom.unop) ?_
  intro d d' φ
  have hc : (IsAffineOverAffineOpen (S := S)).ι.map φ.right.unop ≫ d.hom.unop = d'.hom.unop :=
    congrArg Quiver.Hom.unop (StructuredArrow.w φ)
  refine Eq.trans (h d.right.unop.obj d'.right.unop.obj d.right.unop.property
    d'.right.unop.property d.hom.unop
    ((IsAffineOverAffineOpen (S := S)).ι.map φ.right.unop)) ?_
  rw [hc]

/-- The projection at `f` of `extensionMk P F x h` is `x V hV f`. -/
@[simp]
lemma extensionπ_extensionMk {X : Over S}
    (x : ∀ (V : Over S), IsAffineOverAffineOpen V → (V ⟶ X) →
      (affineExtension P F).obj (op V))
    (h : ∀ (V V' : Over S) (hV : IsAffineOverAffineOpen V) (hV' : IsAffineOverAffineOpen V')
      (f : V ⟶ X) (k : V' ⟶ V),
      (affineExtension P F).map k.op (x V hV f) = x V' hV' (k ≫ f))
    {V : Over S} (hV : IsAffineOverAffineOpen V) (f : V ⟶ X) :
    extensionπ P F hV f (extensionMk P F x h) = x V hV f :=
  Types.Limit.π_mk (affineDiagram P F X) _ _ _


/-- Restriction of a section of a presheaf along a composite is the composite of the two
restrictions. -/
lemma map_map_apply {C : Type*} [Category C] (G : Cᵒᵖ ⥤ Type v) {A B D : C} (a : A ⟶ B)
    (b : B ⟶ D) (z : G.obj (op D)) : G.map a.op (G.map b.op z) = G.map (a ≫ b).op z := by
  rw [op_comp, Functor.map_comp]
  rfl

/-- The restriction map along an identity is the identity. -/
lemma map_id_apply {C : Type*} [Category C] (G : Cᵒᵖ ⥤ Type v) {Z : C} (x : G.obj (op Z)) :
    G.map (𝟙 Z).op x = x := by simp

/-- The image of a composite lies in any open containing the image of the second factor. -/
lemma range_le_of_comp {Z Z' X : Over S} (k : Z' ⟶ Z) (g : Z ⟶ X) (W : X.left.Opens)
    (h : Set.range (⇑g.left) ⊆ (W : Set X.left)) :
    Set.range (⇑(k ≫ g).left) ⊆ (W : Set X.left) := by
  rintro _ ⟨y, rfl⟩
  rw [Over.comp_left]
  exact h (Set.mem_range_self (k.left y))

/-- A finite affine refinement of the preimage of an open covering, for a quasi-compact source. -/
private lemma exists_finite_affine_refinement_preimage {Z Y : Scheme.{u}} [CompactSpace Z]
    (f : Z ⟶ Y) {ι : Type u} (U : ι → Y.Opens) (hU : ⨆ i, U i = ⊤) :
    ∃ (κ : Type u) (_ : Finite κ) (A : κ → Z.Opens) (c : κ → ι),
      (∀ a, IsAffineOpen (A a)) ∧ (∀ a, A a ≤ f ⁻¹ᵁ U (c a)) ∧ ⨆ a, A a = ⊤ :=
  exists_finite_affine_refinement (fun i => f ⁻¹ᵁ U i)
    (by rw [← Scheme.Hom.preimage_iSup, hU]; simp)

/-- **The separatedness of the colimit formula on affine objects.** Two sections over an affine
object of `Sch/S` lying over an affine open of `S` which agree on the members of a finite
covering by affine opens are equal. -/
theorem affineExtension_ext (hP1 : HasAffineOpens P) (hP2 : HasFinitePresentationAffines P)
    (haF : IsZariskiSheafOnSubcategory P F) {Y : Over S} (hY : IsAffineOverAffineOpen Y)
    {κ : Type u} [Finite κ] (U : κ → Y.left.Opens) (hcov : ⨆ a, U a = ⊤)
    (haff : ∀ a, IsAffineOpen (U a)) (x x' : (affineExtension P F).obj (op Y))
    (h : ∀ a, (affineExtension P F).map (overOpenι Y (U a)).op x
      = (affineExtension P F).map (overOpenι Y (U a)).op x') : x = x' := by
  obtain ⟨t, -, huniq⟩ := isSheafForOpens_affineExtension hP1 hP2 haF Y hY U hcov haff
    (fun a => (affineExtension P F).map (overOpenι Y (U a)).op x) (fun a b => by
      rw [map_map_apply, map_map_apply, overOpenLE_comp_overOpenι, overOpenLE_comp_overOpenι])
  rw [huniq x (fun a => rfl), huniq x' (fun a => (h a).symm)]

/-- **The analogue of condition (a) of Stacks 0EUW for the extension.** The extension is a
Zariski sheaf on `Sch/S`: its value at `X` is the limit of the colimit formula over the affine
objects over affine opens of `S` mapping to `X`, and a section is built over each such object by
gluing, using the sheaf condition for the colimit formula on affine objects. -/
@[stacks 0EUW "the analogue of condition (a) for the extension
`AlgebraicGeometry.ExtendingFunctors.extension`: the extension is a Zariski sheaf on `Sch/S`"]
theorem isZariskiSheaf_extension (hP1 : HasAffineOpens P)
    (hP2 : HasFinitePresentationAffines P) (haF : IsZariskiSheafOnSubcategory P F) :
    IsZariskiSheaf (extension P F) := by
  classical
  intro X ι V hV s hs
  obtain ⟨sec, hsecDef, hsecRes, hsecAgr⟩ :
      ∃ sec : ∀ (i : ι) (Z : Over S), IsAffineOverAffineOpen Z → ∀ (g : Z ⟶ X),
          Set.range (⇑g.left) ⊆ (V i : Set X.left) → (affineExtension P F).obj (op Z),
        (∀ (i : ι) (Z : Over S) (hZ : IsAffineOverAffineOpen Z) (g : Z ⟶ X)
            (hr : Set.range (⇑g.left) ⊆ (V i : Set X.left)),
            sec i Z hZ g hr = extensionπ P F hZ (liftOverOpen g (V i) hr) (s i)) ∧
        (∀ (i : ι) (Z Z' : Over S) (hZ : IsAffineOverAffineOpen Z)
            (hZ' : IsAffineOverAffineOpen Z') (g : Z ⟶ X) (k : Z' ⟶ Z)
            (hr : Set.range (⇑g.left) ⊆ (V i : Set X.left))
            (hr' : Set.range (⇑(k ≫ g).left) ⊆ (V i : Set X.left)),
            (affineExtension P F).map k.op (sec i Z hZ g hr) = sec i Z' hZ' (k ≫ g) hr') ∧
        (∀ (i j : ι) (Z : Over S) (hZ : IsAffineOverAffineOpen Z) (g : Z ⟶ X)
            (hr : Set.range (⇑g.left) ⊆ (V i : Set X.left))
            (hr' : Set.range (⇑g.left) ⊆ (V j : Set X.left)),
            sec i Z hZ g hr = sec j Z hZ g hr') := by
    refine ⟨fun i Z hZ g hr => extensionπ P F hZ (liftOverOpen g (V i) hr) (s i),
      fun i Z hZ g hr => rfl, ?_, ?_⟩
    · intro i Z Z' hZ hZ' g k hr hr'
      beta_reduce
      have e : k ≫ liftOverOpen g (V i) hr = liftOverOpen (k ≫ g) (V i) hr' := by
        refine eq_of_comp_overOpenι ?_
        rw [Category.assoc, liftOverOpen_comp_overOpenι, liftOverOpen_comp_overOpenι]
      rw [extensionπ_map P F hZ hZ' k (liftOverOpen g (V i) hr) (s i), e]
    · intro i j Z hZ g hr hr'
      beta_reduce
      have hrij : Set.range (⇑g.left) ⊆ ((V i ⊓ V j : X.left.Opens) : Set X.left) :=
        fun y hy => ⟨hr hy, hr' hy⟩
      have e : ∀ (U : X.left.Opens) (hU : V i ⊓ V j ≤ U) (hrU : Set.range (⇑g.left) ⊆ U),
          liftOverOpen g (V i ⊓ V j) hrij ≫ overOpenLE X hU = liftOverOpen g U hrU := by
        intro U hU hrU
        refine eq_of_comp_overOpenι ?_
        rw [Category.assoc, overOpenLE_comp_overOpenι, liftOverOpen_comp_overOpenι,
          liftOverOpen_comp_overOpenι]
      rw [← e _ inf_le_left hr, ← e _ inf_le_right hr', ← extensionπ_naturality,
        ← extensionπ_naturality, hs i j]
  have hsecCongr : ∀ (i : ι) (Z : Over S) (hZ : IsAffineOverAffineOpen Z) (g g' : Z ⟶ X)
      (e : g = g') (hr : Set.range (⇑g.left) ⊆ (V i : Set X.left))
      (hr' : Set.range (⇑g'.left) ⊆ (V i : Set X.left)),
      sec i Z hZ g hr = sec i Z hZ g' hr' := by
    intro i Z hZ g g' e hr hr'
    subst e
    rfl
  have key : ∀ (i j : ι) (Z Z' : Over S) (hZ : IsAffineOverAffineOpen Z)
      (hZ' : IsAffineOverAffineOpen Z') (g : Z ⟶ X) (k : Z' ⟶ Z) (g' : Z' ⟶ X)
      (e : k ≫ g = g') (hr : Set.range (⇑g.left) ⊆ (V i : Set X.left))
      (hr' : Set.range (⇑g'.left) ⊆ (V j : Set X.left)),
      (affineExtension P F).map k.op (sec i Z hZ g hr) = sec j Z' hZ' g' hr' := by
    intro i j Z Z' hZ hZ' g k g' e hr hr'
    have hrk : Set.range (⇑(k ≫ g).left) ⊆ (V i : Set X.left) := range_le_of_comp k g (V i) hr
    have hrg' : Set.range (⇑g'.left) ⊆ (V i : Set X.left) := by rw [← e]; exact hrk
    rw [hsecRes i Z Z' hZ hZ' g k hr hrk,
      hsecCongr i Z' hZ' (k ≫ g) g' e hrk hrg', hsecAgr i j Z' hZ' g' hrg' hr']
  have hrefine : ∀ (W : Over S), IsAffineOverAffineOpen W → ∀ (f : W ⟶ X),
      ∃ (κ : Type u) (_ : Finite κ) (Wa : κ → W.left.Opens) (cc : κ → ι),
        (∀ a, IsAffineOpen (Wa a)) ∧ (⨆ a, Wa a = ⊤) ∧
        ∀ a, Set.range (⇑(overOpenι W (Wa a) ≫ f).left) ⊆ (V (cc a) : Set X.left) := by
    intro W hW f
    have hWaff : IsAffine W.left := hW.1
    obtain ⟨κ, hκ, Wa, cc, haff, hle, hcovWa⟩ :=
      exists_finite_affine_refinement_preimage f.left V hV
    refine ⟨κ, hκ, Wa, cc, haff, hcovWa, fun a => ?_⟩
    rintro _ ⟨y, rfl⟩
    exact hle a y.2
  have hT : ∀ (W : Over S) (hW : IsAffineOverAffineOpen W) (f : W ⟶ X),
      ∃ t : (affineExtension P F).obj (op W),
        ∀ (Z : Over S) (hZ : IsAffineOverAffineOpen Z) (g : Z ⟶ W) (i : ι)
          (hr : Set.range (⇑(g ≫ f).left) ⊆ (V i : Set X.left)),
          (affineExtension P F).map g.op t = sec i Z hZ (g ≫ f) hr := by
    intro W hW f
    have hWaff : IsAffine W.left := hW.1
    obtain ⟨κ, hκ, Wa, cc, haffWa, hcovWa, hrWa⟩ := hrefine W hW f
    have hcompat : ∀ a b, (affineExtension P F).map
          (overOpenLE W (inf_le_left : Wa a ⊓ Wa b ≤ Wa a)).op
          (sec (cc a) (overOpen W (Wa a)) (isAffineOverAffineOpen_overOpen hW (haffWa a))
            (overOpenι W (Wa a) ≫ f) (hrWa a))
        = (affineExtension P F).map (overOpenLE W (inf_le_right : Wa a ⊓ Wa b ≤ Wa b)).op
          (sec (cc b) (overOpen W (Wa b)) (isAffineOverAffineOpen_overOpen hW (haffWa b))
            (overOpenι W (Wa b) ≫ f) (hrWa b)) := by
      intro a b
      have hiab : IsAffineOverAffineOpen (overOpen W (Wa a ⊓ Wa b)) :=
        isAffineOverAffineOpen_overOpen hW ((haffWa a).inf (haffWa b))
      have emor : ∀ (U : W.left.Opens) (hU : Wa a ⊓ Wa b ≤ U),
          overOpenLE W hU ≫ (overOpenι W U ≫ f) = overOpenι W (Wa a ⊓ Wa b) ≫ f := fun U hU => by
        rw [← Category.assoc, overOpenLE_comp_overOpenι]
      have emor_a := emor (Wa a) inf_le_left
      have emor_b := emor (Wa b) inf_le_right
      have hrab_a : Set.range (⇑(overOpenι W (Wa a ⊓ Wa b) ≫ f).left)
          ⊆ (V (cc a) : Set X.left) := by
        rw [← emor_a]
        exact range_le_of_comp _ _ _ (hrWa a)
      refine Eq.trans (key (cc a) (cc a) (overOpen W (Wa a)) (overOpen W (Wa a ⊓ Wa b))
        (isAffineOverAffineOpen_overOpen hW (haffWa a)) hiab (overOpenι W (Wa a) ≫ f)
        (overOpenLE W (inf_le_left : Wa a ⊓ Wa b ≤ Wa a)) (overOpenι W (Wa a ⊓ Wa b) ≫ f)
        emor_a (hrWa a) hrab_a) ?_
      exact (key (cc b) (cc a) (overOpen W (Wa b)) (overOpen W (Wa a ⊓ Wa b))
        (isAffineOverAffineOpen_overOpen hW (haffWa b)) hiab (overOpenι W (Wa b) ≫ f)
        (overOpenLE W (inf_le_right : Wa a ⊓ Wa b ≤ Wa b)) (overOpenι W (Wa a ⊓ Wa b) ≫ f)
        emor_b (hrWa b) hrab_a).symm
    obtain ⟨t, ht, -⟩ := isSheafForOpens_affineExtension hP1 hP2 haF W hW Wa hcovWa haffWa
      (fun a => sec (cc a) (overOpen W (Wa a))
        (isAffineOverAffineOpen_overOpen hW (haffWa a)) (overOpenι W (Wa a) ≫ f) (hrWa a))
      hcompat
    refine ⟨t, ?_⟩
    intro Z hZ g i hr
    have hZaff : IsAffine Z.left := hZ.1
    obtain ⟨κ', hκ', Za, cc', haffZa, hleZa, hcovZa⟩ :=
      exists_finite_affine_refinement_preimage g.left Wa hcovWa
    refine affineExtension_ext P F hP1 hP2 haF hZ Za hcovZa haffZa _ _ (fun d => ?_)
    have hiZd : IsAffineOverAffineOpen (overOpen Z (Za d)) :=
      isAffineOverAffineOpen_overOpen hZ (haffZa d)
    have hrd : Set.range (⇑(overOpenι Z (Za d) ≫ (g ≫ f)).left) ⊆ (V i : Set X.left) :=
      range_le_of_comp _ _ _ hr
    have e1 : overOpenι Z (Za d) ≫ g
        = overOpenResLE g (hleZa d) ≫ overOpenι W (Wa (cc' d)) :=
      (overOpenResLE_comp_overOpenι g (hleZa d)).symm
    have emor_d : overOpenResLE g (hleZa d) ≫ (overOpenι W (Wa (cc' d)) ≫ f)
        = overOpenι Z (Za d) ≫ (g ≫ f) := by
      rw [← Category.assoc, ← e1, Category.assoc]
    refine Eq.trans ?_ (key i i Z (overOpen Z (Za d)) hZ hiZd (g ≫ f) (overOpenι Z (Za d))
      (overOpenι Z (Za d) ≫ (g ≫ f)) rfl hr hrd).symm
    rw [map_map_apply, e1, ← map_map_apply, ht (cc' d)]
    exact key (cc (cc' d)) i (overOpen W (Wa (cc' d))) (overOpen Z (Za d))
      (isAffineOverAffineOpen_overOpen hW (haffWa (cc' d))) hiZd
      (overOpenι W (Wa (cc' d)) ≫ f) (overOpenResLE g (hleZa d))
      (overOpenι Z (Za d) ≫ (g ≫ f)) emor_d (hrWa (cc' d)) hrd
  choose T hT' using hT
  have hTcompat : ∀ (W W' : Over S) (hW : IsAffineOverAffineOpen W)
      (hW' : IsAffineOverAffineOpen W') (f : W ⟶ X) (k : W' ⟶ W),
      (affineExtension P F).map k.op (T W hW f) = T W' hW' (k ≫ f) := by
    intro W W' hW hW' f k
    have hW'aff : IsAffine W'.left := hW'.1
    obtain ⟨κ, hκ, Wa, cc, haffWa, hcovWa, hrWa⟩ := hrefine W' hW' (k ≫ f)
    refine affineExtension_ext P F hP1 hP2 haF hW' Wa hcovWa haffWa _ _ (fun a => ?_)
    have hiWa : IsAffineOverAffineOpen (overOpen W' (Wa a)) :=
      isAffineOverAffineOpen_overOpen hW' (haffWa a)
    have eassoc : (overOpenι W' (Wa a) ≫ k) ≫ f = overOpenι W' (Wa a) ≫ (k ≫ f) :=
      Category.assoc _ _ _
    have hr1 : Set.range (⇑((overOpenι W' (Wa a) ≫ k) ≫ f).left) ⊆ (V (cc a) : Set X.left) := by
      rw [eassoc]
      exact hrWa a
    rw [map_map_apply, hT' W hW f (overOpen W' (Wa a)) hiWa (overOpenι W' (Wa a) ≫ k) (cc a) hr1,
      hT' W' hW' (k ≫ f) (overOpen W' (Wa a)) hiWa (overOpenι W' (Wa a)) (cc a) (hrWa a)]
    exact hsecCongr (cc a) (overOpen W' (Wa a)) hiWa _ _ eassoc hr1 (hrWa a)
  refine ⟨extensionMk P F (fun W hW f => T W hW f) hTcompat, fun i => ?_, fun t' ht' => ?_⟩
  · refine extension_ext P F _ _ (fun Z hZ g => ?_)
    rw [extensionπ_naturality, extensionπ_extensionMk]
    have hr2 : Set.range (⇑(g ≫ overOpenι X (V i)).left) ⊆ (V i : Set X.left) := by
      rintro _ ⟨y, rfl⟩
      exact (g.left y).2
    have hr1 : Set.range (⇑(𝟙 Z ≫ (g ≫ overOpenι X (V i))).left) ⊆ (V i : Set X.left) := by
      rwa [Category.id_comp]
    have h1 := hT' Z hZ (g ≫ overOpenι X (V i)) Z hZ (𝟙 Z) i hr1
    rw [map_id_apply] at h1
    have h2 : sec i Z hZ (𝟙 Z ≫ (g ≫ overOpenι X (V i))) hr1
        = sec i Z hZ (g ≫ overOpenι X (V i)) hr2 :=
      hsecCongr i Z hZ _ _ (Category.id_comp _) hr1 hr2
    have hlift : liftOverOpen (g ≫ overOpenι X (V i)) (V i) hr2 = g := by
      refine eq_of_comp_overOpenι ?_
      rw [liftOverOpen_comp_overOpenι]
    rw [show T Z hZ (g ≫ overOpenι X (V i)) = _ from h1, h2, hsecDef, hlift]
  · refine extension_ext P F _ _ (fun Z hZ f => ?_)
    rw [extensionπ_extensionMk]
    obtain ⟨κ, hκ, Za, cc, haffZa, hcovZa, hrZa⟩ := hrefine Z hZ f
    refine affineExtension_ext P F hP1 hP2 haF hZ Za hcovZa haffZa _ _ (fun a => ?_)
    have hiZa : IsAffineOverAffineOpen (overOpen Z (Za a)) :=
      isAffineOverAffineOpen_overOpen hZ (haffZa a)
    have efac : overOpenι Z (Za a) ≫ f
        = liftOverOpen (overOpenι Z (Za a) ≫ f) (V (cc a)) (hrZa a)
          ≫ overOpenι X (V (cc a)) :=
      (liftOverOpen_comp_overOpenι _ _ _).symm
    rw [extensionπ_map P F hZ hiZa (overOpenι Z (Za a)) f t', efac, ← extensionπ_naturality,
      ht' (cc a),
      hT' Z hZ f (overOpen Z (Za a)) hiZa (overOpenι Z (Za a)) (cc a) (hrZa a), hsecDef]

end Extension

end AlgebraicGeometry.ExtendingFunctors

end
