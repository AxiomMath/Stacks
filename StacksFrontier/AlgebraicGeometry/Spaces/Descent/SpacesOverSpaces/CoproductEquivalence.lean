module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Sites.LeftExact
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.SpacesOverSpaces.DescentTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.SpacesOverSpaces.Products
public import StacksFrontier.AlgebraicGeometry.Spaces.Glueing.SheafCoproduct

/-!
# Descent data for a family as descent data for its coproduct

If the sheaf coproduct of a family of algebraic spaces is an algebraic space, then descent data
for the family whose underlying spaces have algebraic sheaf coproduct are canonically
equivalent to descent data for the single coproduct morphism.

## Main definitions

* `AlgebraicGeometry.Space.Descent.spaceSheaf` views an algebraic space as a sheaf on the big
  fppf site.
* `AlgebraicGeometry.Space.Descent.AlgebraicSheafCoproduct` is a colimit cocone in sheaves
  whose vertex carries a scheme atlas, hence is an algebraic space.
* `AlgebraicGeometry.Space.Descent.AlgebraicCoproductDescentData` is the full subcategory of
  descent data whose underlying spaces have an algebraic sheaf coproduct.
* `AlgebraicGeometry.Space.Descent.gluingPullbackIso` transports a gluing isomorphism to the
  literal fibre products of presheaves.
* `AlgebraicGeometry.Space.Descent.FamilyCoproductEquivalence` records the canonical
  equivalence together with its action on objects, gluing isomorphisms and morphisms.

## Main results

* `AlgebraicGeometry.Space.Descent.familyCoproductEquivalence` is the canonical equivalence on
  the descent data admitting an algebraic sheaf coproduct, relative to a given algebraic sheaf
  coproduct of the sources.

## Implementation notes

Descent data for a single morphism are represented by the one-member family indexed by
`PUnit`. The object is identified with the sheaf coproduct of the family of objects. The gluing
isomorphism is compared on each pair of summands with the original one, and componentwise
morphisms are sent to their sheaf coproduct. Both comparison maps are specified by their two
pullback projections, which pins them uniquely by
`CategoryTheory.Limits.pullback.hom_ext`. They are moreover required to be jointly epimorphic
onto sheaves, which is the observation that a fibre product of coproducts is the coproduct of
the pairwise fibre products; that is what makes the per-pair gluing equation a complete
description of the glued isomorphism rather than merely a compatibility. Coproducts are
supplied as colimit cocones in sheaves, so neither a sheafification instance nor a smallness
assumption on the index type is needed. The algebraicity conditions retain the size scope of
the fixed big fppf site: of the three parts of
`AlgebraicGeometry.IsAlgebraicSpace` only the atlas is assumed of a coproduct, the sheaf
condition and the representability of the diagonal being consequences of the colimit property,
and by Stacks 02WQ the atlas is exactly the part that can fail when the index type is large.

## References

* [Stacks Project, Tag 0ADK](https://stacks.math.columbia.edu/tag/0ADK)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.Space.Descent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}}
  {hS : B.Contains S}

/-- An algebraic space regarded as a sheaf on the big fppf site. -/
public abbrev spaceSheaf (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X) :
    Sheaf (BigFppfOver.topology B S hS) (Type u) :=
  ⟨X, hX.isSheaf⟩

/-- A coproduct in sheaves of a family of algebraic spaces, together with a scheme atlas of
the coproduct. The colimit cocone specifies the coproduct without assuming sheafification on
the site, and `AlgebraicGeometry.Space.Descent.AlgebraicSheafCoproduct.isAlgebraicSpace`
recovers algebraicity of the vertex from the atlas. -/
public structure AlgebraicSheafCoproduct {I : Type v}
    (X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : ∀ i, IsAlgebraicSpace B S hS (X i)) where
  /-- The coproduct sheaf. -/
  sheaf : Sheaf (BigFppfOver.topology B S hS) (Type u)
  /-- The canonical summand inclusions. -/
  ι (i : I) : spaceSheaf (X i) (hX i) ⟶ sheaf
  /-- The coproduct universal property in sheaves. -/
  isColimit : IsColimit (Cofan.mk sheaf ι)
  /-- A scheme atlas of the coproduct, surjective and étale after every representable base
  change. This is the only part of algebraicity that is not already a consequence of the
  colimit property: by Stacks 02WQ a coproduct of algebraic spaces is an algebraic space
  exactly when such an atlas exists inside the fixed big site, which is a genuine restriction
  on the size of the index type. -/
  exists_atlas : ∃ (U : BigFppfOver B S hS) (g : yoneda.obj U ⟶ sheaf.obj),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) g ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) g

namespace AlgebraicSheafCoproduct

variable {I : Type v} {X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {hX : ∀ i, IsAlgebraicSpace B S hS (X i)}

/-- **The vertex of an algebraic sheaf coproduct is an algebraic space.**

It is a sheaf because it is an object of the sheaf category, its diagonal is representable by
`AlgebraicGeometry.relativelyRepresentable_diag_of_isColimit_cofan`, and an atlas is the
remaining field. -/
public lemma isAlgebraicSpace (Y : AlgebraicSheafCoproduct X hX) :
    IsAlgebraicSpace B S hS Y.sheaf.obj :=
  ⟨Y.sheaf.property,
    relativelyRepresentable_diag_of_isColimit_cofan Y.ι Y.isColimit
      fun i => (hX i).diagonal_representable,
    Y.exists_atlas⟩

/-- The underlying presheaf map induced by maps from the summands to a sheaf. -/
public noncomputable def desc (Y : AlgebraicSheafCoproduct X hX)
    (T : Sheaf (BigFppfOver.topology B S hS) (Type u))
    (f : ∀ i, X i ⟶ T.obj) : Y.sheaf.obj ⟶ T.obj :=
  (Y.isColimit.desc (Cofan.mk T (fun i => ⟨f i⟩))).hom

/-- The induced map restricts to the given map on each summand. -/
@[reassoc (attr := simp)]
public lemma ι_desc (Y : AlgebraicSheafCoproduct X hX)
    (T : Sheaf (BigFppfOver.topology B S hS) (Type u))
    (f : ∀ i, X i ⟶ T.obj) (i : I) :
    (Y.ι i).hom ≫ Y.desc T f = f i :=
  congrArg (fun g => g.hom)
    (Y.isColimit.fac (Cofan.mk T (fun i => ⟨f i⟩)) ⟨i⟩)

/-- The coproduct of a family of maps, taken in sheaves and then forgotten to presheaves. -/
public noncomputable def map {X' : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hX' : ∀ i, IsAlgebraicSpace B S hS (X' i)}
    (Y : AlgebraicSheafCoproduct X hX) (Y' : AlgebraicSheafCoproduct X' hX')
    (g : ∀ i, X i ⟶ X' i) : Y.sheaf.obj ⟶ Y'.sheaf.obj :=
  Y.desc Y'.sheaf (fun i => g i ≫ (Y'.ι i).hom)

/-- Two maps out of a sheaf coproduct agreeing on every summand are equal. -/
public lemma desc_ext (Y : AlgebraicSheafCoproduct X hX)
    (T : Sheaf (BigFppfOver.topology B S hS) (Type u))
    {g h : Y.sheaf.obj ⟶ T.obj}
    (hh : ∀ i, (Y.ι i).hom ≫ g = (Y.ι i).hom ≫ h) : g = h :=
  congrArg (fun k : Y.sheaf ⟶ T => k.hom) <|
    Y.isColimit.hom_ext fun i => Sheaf.hom_ext (hh i.as)

/-- The coproduct of a family of maps restricts to the given map on each summand. -/
public lemma ι_map {X' : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hX' : ∀ i, IsAlgebraicSpace B S hS (X' i)}
    (Y : AlgebraicSheafCoproduct X hX) (Y' : AlgebraicSheafCoproduct X' hX')
    (g : ∀ i, X i ⟶ X' i) (i : I) :
    (Y.ι i).hom ≫ Y.map Y' g = g i ≫ (Y'.ι i).hom :=
  Y.ι_desc _ _ _

private lemma map_id (Y : AlgebraicSheafCoproduct X hX) :
    Y.map Y (fun i => 𝟙 (X i)) = 𝟙 Y.sheaf.obj := by
  refine desc_ext Y Y.sheaf fun i => ?_
  rw [ι_map]
  simp

private lemma map_comp {X' X'' : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hX' : ∀ i, IsAlgebraicSpace B S hS (X' i)}
    {hX'' : ∀ i, IsAlgebraicSpace B S hS (X'' i)}
    (Y : AlgebraicSheafCoproduct X hX) (Y' : AlgebraicSheafCoproduct X' hX')
    (Y'' : AlgebraicSheafCoproduct X'' hX'')
    (g : ∀ i, X i ⟶ X' i) (h : ∀ i, X' i ⟶ X'' i) :
    Y.map Y' g ≫ Y'.map Y'' h = Y.map Y'' (fun i => g i ≫ h i) := by
  refine desc_ext Y Y''.sheaf fun i => ?_
  simp only [← Category.assoc, ι_map]
  simp only [Category.assoc, ι_map]

end AlgebraicSheafCoproduct

/-!
### Local use of a sheaf coproduct

The coproduct universal property gives local factorization of every section through one of
the summands. This is the sheaf level bridge used to compare fibre products componentwise.
-/

/-- A map out of a coproduct sending the `i`-th summand into the left summand of `F i ⨿ c.pt`
and every other summand into the right one. -/
private def cofan_desc_inl
    {C : Type*} [Category* C] [FinitaryExtensive C]
    {I : Type*} {F : I → C} (c : Cofan F) (hc : IsColimit c) (i : I) :
    {d : c.pt ⟶ F i ⨿ c.pt // c.inj i ≫ d = coprod.inl ∧
      ∀ j, j ≠ i → c.inj j ≫ d = c.inj j ≫ coprod.inr} := by
  classical
  let t (k : I) : F k ⟶ F i ⨿ c.pt :=
    if h : k = i then eqToHom (congrArg F h) ≫ coprod.inl else c.inj k ≫ coprod.inr
  refine ⟨Cofan.IsColimit.desc hc t, ?_, fun j hj => ?_⟩
  · simpa only [t, dite_eq_left rfl, eqToHom_refl, Category.id_comp] using
      Cofan.IsColimit.fac hc t i
  · simpa only [t, dite_eq_right hj] using Cofan.IsColimit.fac hc t j

private lemma cofan_inj_mono
    {C : Type*} [Category* C] [FinitaryExtensive C]
    {I : Type*} {F : I → C} (c : Cofan F) (hc : IsColimit c) (i : I) :
    Mono (c.inj i) := by
  obtain ⟨d, hd, -⟩ := cofan_desc_inl c hc i
  have : Mono (c.inj i ≫ d) := hd ▸ inferInstance
  exact mono_of_mono (c.inj i) d

private def cofan_overlap_isInitial
    {C : Type*} [Category* C] [FinitaryExtensive C]
    {I : Type*} {F : I → C} (c : Cofan F) (hc : IsColimit c)
    {i j : I} (hij : i ≠ j) {P : C} (a : P ⟶ F i) (b : P ⟶ F j)
    (hab : a ≫ c.inj i = b ≫ c.inj j) : IsInitial P := by
  obtain ⟨d, hi, hd⟩ := cofan_desc_inl c hc i
  have heq : a ≫ coprod.inl = (b ≫ c.inj j) ≫ coprod.inr := by
    rw [← hi, ← Category.assoc, hab, Category.assoc, hd j hij.symm, Category.assoc]
  let hp := FinitaryExtensive.isPullback_initial_to_binaryCofan
    (coprodIsCoprod (F i) c.pt)
  exact IsInitial.ofStrict (hp.lift a (b ≫ c.inj j) heq) initialIsInitial

private lemma pullbackCoproduct_locally_factors
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {I : Type v} {Fi : I → Sheaf J (Type u)} {G Y : Sheaf J (Type u)}
    (ι : ∀ i, Fi i ⟶ G) (hc : IsColimit (Cofan.mk G ι)) (f : Y ⟶ G)
    {H : I → Sheaf J (Type u)} (p : ∀ i, H i ⟶ Y) (q : ∀ i, H i ⟶ Fi i)
    (hP : ∀ i, IsPullback (p i) (q i) f (ι i))
    {T : C} (y : Y.obj.obj (Opposite.op T)) :
    ∃ (R : Sieve T), R ∈ J T ∧ ∀ ⦃V : C⦄ (a : V ⟶ T), R a →
      ∃ (i : I) (z : (H i).obj.obj (Opposite.op V)),
        (p i).hom.app (Opposite.op V) z = Y.obj.map a.op y := by
  classical
  obtain ⟨R, hR, hloc⟩ := coproduct_locally_factors Fi G ι hc
    ((f.hom.app (Opposite.op T)) y)
  refine ⟨R, hR, fun V a ha => ?_⟩
  obtain ⟨i, x, hx⟩ := hloc a ha
  let α : yoneda.obj V ⟶ Y.obj := yonedaEquiv.symm (Y.obj.map a.op y)
  let β : yoneda.obj V ⟶ (Fi i).obj := yonedaEquiv.symm x
  have hαβ : α ≫ f.hom = β ≫ (ι i).hom := by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, yonedaEquiv_comp]
    simp only [α, β, Equiv.apply_symm_apply]
    rw [NatTrans.naturality_apply]
    exact hx.symm
  let hP' := (hP i).map (sheafToPresheaf J (Type u))
  let ℓ : yoneda.obj V ⟶ (H i).obj := hP'.lift α β hαβ
  refine ⟨i, yonedaEquiv ℓ, ?_⟩
  have hv := congrArg yonedaEquiv (hP'.lift_fst α β hαβ : ℓ ≫ (p i).hom = α)
  rw [yonedaEquiv_comp] at hv
  simpa [α] using hv

private lemma sheafSections_ext
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    (Z : Sheaf J (Type u)) {T : C} {R : Sieve T} (hR : R ∈ J T)
    (x y : Z.obj.obj (Opposite.op T))
    (h : ∀ ⦃V : C⦄ (a : V ⟶ T), R a →
      Z.obj.map a.op x = Z.obj.map a.op y) : x = y :=
  (Z.property.isSheafFor R hR).isSeparatedFor.ext (fun _ a ha ↦ h a ha)

private lemma hom_ext_of_locally_surjective
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {I : Type v} {Q : I → Sheaf J (Type u)} {P W : Sheaf J (Type u)}
    (m : ∀ i, Q i ⟶ P)
    (hlocal : ∀ {T : C} (x : P.obj.obj (Opposite.op T)),
      ∃ (R : Sieve T), R ∈ J T ∧ ∀ ⦃V : C⦄ (a : V ⟶ T), R a →
        ∃ (i : I) (z : (Q i).obj.obj (Opposite.op V)),
          (m i).hom.app (Opposite.op V) z = P.obj.map a.op x)
    {g h : P ⟶ W}
    (hgh : ∀ i, m i ≫ g = m i ≫ h) : g = h := by
  apply Sheaf.hom_ext
  ext T x
  obtain ⟨R, hR, hlocal⟩ := hlocal x
  refine sheafSections_ext W hR _ _ fun V a ha => ?_
  obtain ⟨i, z, hz⟩ := hlocal a ha
  calc
    W.obj.map a.op ((g.hom.app T) x) =
        (g.hom.app (Opposite.op V)) (P.obj.map a.op x) :=
      (NatTrans.naturality_apply g.hom a.op x).symm
    _ = (h.hom.app (Opposite.op V)) (P.obj.map a.op x) := by
      rw [← hz]
      exact congrArg (fun φ : Q i ⟶ W => φ.hom.app (Opposite.op V) z) (hgh i)
    _ = W.obj.map a.op ((h.hom.app T) x) := NatTrans.naturality_apply h.hom a.op x

private lemma exists_unique_desc_section
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {I : Type v} {Q : I → Sheaf J (Type u)} {P W : Sheaf J (Type u)}
    (m : ∀ i, Q i ⟶ P) (k : ∀ i, Q i ⟶ W)
    (hlocal : ∀ {T : C} (x : P.obj.obj (Opposite.op T)),
      ∃ (R : Sieve T), R ∈ J T ∧ ∀ ⦃V : C⦄ (a : V ⟶ T), R a →
        ∃ (i : I) (z : (Q i).obj.obj (Opposite.op V)),
          (m i).hom.app (Opposite.op V) z = P.obj.map a.op x)
    (hcompat : ∀ {U : C} (i j : I)
      (x : (Q i).obj.obj (Opposite.op U)) (y : (Q j).obj.obj (Opposite.op U)),
      (m i).hom.app (Opposite.op U) x = (m j).hom.app (Opposite.op U) y →
      (k i).hom.app (Opposite.op U) x = (k j).hom.app (Opposite.op U) y)
    {U : C} (x : P.obj.obj (Opposite.op U)) :
    ∃! w : W.obj.obj (Opposite.op U),
      ∀ ⦃V : C⦄ (a : V ⟶ U) (i : I) (z : (Q i).obj.obj (Opposite.op V)),
        (m i).hom.app (Opposite.op V) z = P.obj.map a.op x →
        W.obj.map a.op w = (k i).hom.app (Opposite.op V) z := by
  classical
  obtain ⟨R, hR, hloc⟩ := hlocal x
  choose idx sec hsec using hloc
  let t : Presieve.FamilyOfElements W.obj R.arrows :=
    fun V a ha => (k (idx a ha)).hom.app (Opposite.op V) (sec a ha)
  have ht : t.SieveCompatible := by
    intro V V' a ha b
    dsimp [t]
    rw [← NatTrans.naturality_apply]
    apply hcompat
    rw [NatTrans.naturality_apply, hsec, hsec]
    simp [Functor.map_comp]
  have htc := (Presieve.compatible_iff_sieveCompatible t).2 ht
  let w := (W.property.isSheafFor R hR).amalgamate t htc
  have hw : ∀ ⦃V : C⦄ (a : V ⟶ U) (i : I)
      (z : (Q i).obj.obj (Opposite.op V)),
      (m i).hom.app (Opposite.op V) z = P.obj.map a.op x →
      W.obj.map a.op w = (k i).hom.app (Opposite.op V) z := by
    intro V a i z hz
    apply sheafSections_ext W (J.pullback_stable a hR)
    intro V' b hb
    have hba : R (b ≫ a) := hb
    change W.obj.map b.op (W.obj.map a.op w) =
      W.obj.map b.op ((k i).hom.app (Opposite.op V) z)
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
      (W.property.isSheafFor R hR).valid_glue htc (b ≫ a) hba]
    dsimp [t]
    rw [← NatTrans.naturality_apply]
    apply hcompat
    rw [hsec, NatTrans.naturality_apply, hz]
    simp [Functor.map_comp]
  refine ⟨w, hw, fun w' hw' => sheafSections_ext W hR _ _ fun V a ha => ?_⟩
  rw [hw' a (idx a ha) (sec a ha) (hsec a ha),
    hw a (idx a ha) (sec a ha) (hsec a ha)]

private def sheafFamilyDesc
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {I : Type v} {Q : I → Sheaf J (Type u)} {P W : Sheaf J (Type u)}
    (m : ∀ i, Q i ⟶ P) (k : ∀ i, Q i ⟶ W)
    (hlocal : ∀ {T : C} (x : P.obj.obj (Opposite.op T)),
      ∃ (R : Sieve T), R ∈ J T ∧ ∀ ⦃V : C⦄ (a : V ⟶ T), R a →
        ∃ (i : I) (z : (Q i).obj.obj (Opposite.op V)),
          (m i).hom.app (Opposite.op V) z = P.obj.map a.op x)
    (hcompat : ∀ {U : C} (i j : I)
      (x : (Q i).obj.obj (Opposite.op U)) (y : (Q j).obj.obj (Opposite.op U)),
      (m i).hom.app (Opposite.op U) x = (m j).hom.app (Opposite.op U) y →
      (k i).hom.app (Opposite.op U) x = (k j).hom.app (Opposite.op U) y) :
    {d : P ⟶ W // ∀ i, m i ≫ d = k i} := by
  classical
  let h := fun {U} x => exists_unique_desc_section m k hlocal hcompat (U := U) x
  let d (U : Cᵒᵖ) (x : P.obj.obj U) := (h x).choose
  have hd {U : C} (x : P.obj.obj (Opposite.op U)) := (h x).choose_spec.1
  refine ⟨⟨{ app := fun U => ↾(d U), naturality := ?_ }⟩, ?_⟩
  · intro U V a
    ext x
    change d V (P.obj.map a x) = W.obj.map a (d U x)
    apply ((h (P.obj.map a x)).choose_spec.2 _ ?_).symm
    intro Z b i z hz
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    apply hd x (b ≫ a.unop) i z
    simpa [Functor.map_comp] using hz
  · intro i
    apply Sheaf.hom_ext
    ext U x
    simpa [d] using hd ((m i).hom.app U x) (𝟙 U.unop) i x (by simp)

/-- **Coproducts of sheaves of types are universal.** If `G` is the coproduct of a family
`F i` of sheaves and each `H i` sits in a pullback square over `f : Y ⟶ G` and the summand
inclusion `ι i`, then `Y` is the coproduct of the `H i`. The squares are supplied, so no
pullbacks need exist in the sheaf category, and the index type is of arbitrary size. -/
public def pullbackCofanIsColimit
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    [HasSheafify J (Type u)]
    {I : Type v} {F : I → Sheaf J (Type u)} {G Y : Sheaf J (Type u)}
    (ι : ∀ i, F i ⟶ G) (hc : IsColimit (Cofan.mk G ι)) (f : Y ⟶ G)
    {H : I → Sheaf J (Type u)} (p : ∀ i, H i ⟶ Y) (q : ∀ i, H i ⟶ F i)
    (hp : ∀ i, IsPullback (p i) (q i) f (ι i)) :
    IsColimit (Cofan.mk Y p) := private_decl% (by
  classical
  have hl := fun {U : C} (x : Y.obj.obj (Opposite.op U)) =>
    pullbackCoproduct_locally_factors ι hc f p q hp x
  have compat (W : Sheaf J (Type u)) (k : ∀ i, H i ⟶ W)
      {U : C} (i j : I) (x : (H i).obj.obj (Opposite.op U))
      (y : (H j).obj.obj (Opposite.op U))
      (hxy : (p i).hom.app (Opposite.op U) x = (p j).hom.app (Opposite.op U) y) :
      (k i).hom.app (Opposite.op U) x = (k j).hom.app (Opposite.op U) y := by
    by_cases hij : i = j
    · subst j
      have hi : Mono (ι i) := cofan_inj_mono _ hc i
      have hpi : Mono (p i) := MorphismProperty.of_isPullback (hp i).flip hi
      have hm : Mono (p i).hom := (sheafToPresheaf J (Type u)).map_mono (p i)
      have hm' : Mono ((p i).hom.app (Opposite.op U)) := inferInstance
      exact congrArg ((k i).hom.app (Opposite.op U))
        (CategoryTheory.injective_of_mono ((p i).hom.app _) hxy)
    · let A := pullback (p i) (p j)
      have ha : IsInitial A := cofan_overlap_isInitial (Cofan.mk G ι) hc hij
        (pullback.fst (p i) (p j) ≫ q i)
        (pullback.snd (p i) (p j) ≫ q j) (by
          simp only [Category.assoc, cofan_mk_inj, ← (hp i).w, ← (hp j).w]
          exact pullback.condition_assoc f)
      let α : yoneda.obj U ⟶ (H i).obj := yonedaEquiv.symm x
      let β : yoneda.obj U ⟶ (H j).obj := yonedaEquiv.symm y
      have hαβ : α ≫ (p i).hom = β ≫ (p j).hom := by
        apply yonedaEquiv.injective
        simpa only [yonedaEquiv_comp, α, β, Equiv.apply_symm_apply] using hxy
      let hpb := (IsPullback.of_hasPullback (p i) (p j)).map
        (sheafToPresheaf J (Type u))
      let ℓ := hpb.lift α β hαβ
      have heq := congrArg (fun t : A ⟶ W => yonedaEquiv (ℓ ≫ t.hom))
        (ha.hom_ext (pullback.fst (p i) (p j) ≫ k i)
          (pullback.snd (p i) (p j) ≫ k j))
      change yonedaEquiv ((ℓ ≫ (pullback.fst (p i) (p j)).hom) ≫ (k i).hom) =
        yonedaEquiv ((ℓ ≫ (pullback.snd (p i) (p j)).hom) ≫ (k j).hom) at heq
      have hfst : ℓ ≫ (pullback.fst (p i) (p j)).hom = α := hpb.lift_fst α β hαβ
      have hsnd : ℓ ≫ (pullback.snd (p i) (p j)).hom = β := hpb.lift_snd α β hαβ
      rw [hfst, hsnd] at heq
      simpa only [yonedaEquiv_comp, α, β, Equiv.apply_symm_apply] using heq
  let desc (W : Sheaf J (Type u)) (k : ∀ i, H i ⟶ W) :=
    sheafFamilyDesc p k hl (compat W k)
  refine Cofan.IsColimit.mk _ (fun s => (desc s.pt s.inj).1) (fun s => (desc s.pt s.inj).2) ?_
  intro s m hm
  refine hom_ext_of_locally_surjective p hl fun i => ?_
  rw [(desc s.pt s.inj).2 i]
  exact hm i)

private lemma sheafCofan_universal
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    [HasSheafify J (Type u)] {I : Type v} {F : I → Sheaf J (Type u)}
    (c : Cofan F) (hc : IsColimit c) : IsUniversalColimit c := by
  intro F' c' α f h hα hp
  let d : Cofan (fun i => F'.obj ⟨i⟩) := Cofan.mk c'.pt (fun i => c'.ι.app ⟨i⟩)
  have hd : IsColimit d := pullbackCofanIsColimit c.inj hc f
    (fun i => c'.ι.app ⟨i⟩) (fun i => α.app ⟨i⟩) (fun i => hp ⟨i⟩)
  have e : (Cocone.precompose Discrete.natIsoFunctor.symm.hom).obj c' ≅ d :=
    Cocone.ext (Iso.refl _) (by intro j; simp [d])
  exact ⟨(IsColimit.precomposeHomEquiv Discrete.natIsoFunctor.symm c')
    (IsColimit.ofIsoColimit hd e.symm)⟩

private lemma cofan_map_isPullback
    {C : Type*} [Category* C] [FinitaryExtensive C] [HasPullbacks C] [Balanced C]
    {I : Type*} {A B : I → C} {c : Cofan A} {d : Cofan B}
    (hc : IsColimit c) (hd : IsColimit d) (hu : IsUniversalColimit c)
    (f : c.pt ⟶ d.pt) (α : ∀ i, A i ⟶ B i)
    (hα : ∀ i, c.inj i ≫ f = α i ≫ d.inj i) (i : I) :
    IsPullback (c.inj i) (α i) f (d.inj i) := by
  classical
  let P := pullback f (d.inj i)
  let r : A i ⟶ P := pullback.lift (c.inj i) (α i) (hα i)
  have hi : Mono (c.inj i) := cofan_inj_mono c hc i
  have hdi : Mono (d.inj i) := cofan_inj_mono d hd i
  have hr : Mono r := by
    have hh : Mono (r ≫ pullback.fst f (d.inj i)) := by
      simpa only [r, pullback.lift_fst] using hi
    exact mono_of_mono r (pullback.fst f (d.inj i))
  let Q (j : I) := pullback (c.inj j ≫ f) (d.inj i)
  let m (j : I) : Q j ⟶ P := pullback.map _ _ _ _
    (c.inj j) (𝟙 _) (𝟙 _) (by simp) (by simp)
  have hm : IsColimit (Cofan.mk P m) := by
    apply Nonempty.some
    refine hu.nonempty_isColimit_of_isPullback_right
      (fun j => c.inj j ≫ f) f (d.inj i)
      (fun j => pullback.fst (c.inj j ≫ f) (d.inj i))
      (fun j => pullback.snd (c.inj j ≫ f) (d.inj i))
      (fun j => IsPullback.of_hasPullback _ _)
      (IsPullback.of_hasPullback _ _) (Cofan.mk P m) (Iso.refl _)
      (fun _ => rfl)
      (by intro j; simp only [m, cofan_mk_inj, Iso.refl_hom, Category.id_comp]
          exact pullback.lift_fst _ _ _)
      (by intro j; simp only [m, cofan_mk_inj, Iso.refl_hom, Category.id_comp]
          rw [pullback.lift_snd, Category.comp_id])
  have hre : Epi r := by
    refine ⟨fun g h hgh => Cofan.IsColimit.hom_ext hm _ _ fun j => ?_⟩
    change m j ≫ g = m j ≫ h
    by_cases hji : j = i
    · subst j
      have hmi : m i = pullback.fst (c.inj i ≫ f) (d.inj i) ≫ r := by
        apply pullback.hom_ext
        · simp only [m, r, Category.assoc]
          rw [pullback.lift_fst, pullback.lift_fst]
        · apply (cancel_mono (d.inj i)).mp
          simp only [Category.assoc, r, pullback.lift_snd]
          simp only [m, pullback.lift_snd_assoc, Category.comp_id]
          rw [← hα i, pullback.condition]
      rw [hmi, Category.assoc, Category.assoc, hgh]
    · have hQ : IsInitial (Q j) := cofan_overlap_isInitial d hd hji
        (pullback.fst (c.inj j ≫ f) (d.inj i) ≫ α j)
        (pullback.snd (c.inj j ≫ f) (d.inj i)) (by
          rw [Category.assoc, ← hα j, pullback.condition])
      exact hQ.hom_ext _ _
  have : IsIso r := isIso_of_mono_of_epi r
  exact IsPullback.of_iso_pullback ⟨hα i⟩ (asIso r)
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

private lemma overProduct_isSheaf
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {T : Cᵒᵖ ⥤ Type u} (hT : Presheaf.IsSheaf J T) {A B : Over T}
    (hA : Presheaf.IsSheaf J A.left) (hB : Presheaf.IsSheaf J B.left) :
    Presheaf.IsSheaf J (A ⨯ B).left := by
  apply ObjectProperty.prop_of_isLimit (Presheaf.IsSheaf J)
    (Over.isPullback_of_binaryFan_isLimit _ (prodIsProd A B)).isLimit
  rintro (_ | _ | _)
  exacts [hT, hA, hB]

private structure SheafColimit
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    {T : Cᵒᵖ ⥤ Type u} {I : Type v} {A : I → Over T} (c : Cofan A) where
  obj_isSheaf (i : I) : Presheaf.IsSheaf J (A i).left
  pt_isSheaf : Presheaf.IsSheaf J c.pt.left
  isColimit : IsColimit (Cofan.mk
    (⟨c.pt.left, pt_isSheaf⟩ : Sheaf J (Type u))
    (fun i => (⟨(c.inj i).left⟩ :
      (⟨(A i).left, obj_isSheaf i⟩ : Sheaf J (Type u)) ⟶ _)))

private def SheafColimit.desc
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {T : Cᵒᵖ ⥤ Type u} {I : Type v} {A : I → Over T} {c : Cofan A}
    (hc : SheafColimit J c) (hT : Presheaf.IsSheaf J T)
    {Z : Over T} (hZ : Presheaf.IsSheaf J Z.left) (f : ∀ i, A i ⟶ Z) :
    c.pt ⟶ Z := by
  let d := Cofan.IsColimit.desc hc.isColimit
    (fun i => (⟨(f i).left⟩ :
      (⟨(A i).left, hc.obj_isSheaf i⟩ : Sheaf J (Type u)) ⟶ ⟨Z.left, hZ⟩))
  refine Over.homMk d.hom ?_
  change (⟨d.hom ≫ Z.hom⟩ : (⟨c.pt.left, hc.pt_isSheaf⟩ : Sheaf J (Type u)) ⟶
    ⟨T, hT⟩).hom = (⟨c.pt.hom⟩ : (⟨c.pt.left, hc.pt_isSheaf⟩ : Sheaf J (Type u)) ⟶
    ⟨T, hT⟩).hom
  congr 1
  apply Cofan.IsColimit.hom_ext hc.isColimit
  intro i
  apply Sheaf.hom_ext
  change (c.inj i).left ≫ d.hom ≫ Z.hom = (c.inj i).left ≫ c.pt.hom
  have hd := congrArg (fun f => f.hom) (Cofan.IsColimit.fac hc.isColimit
    (fun i => (⟨(f i).left⟩ :
      (⟨(A i).left, hc.obj_isSheaf i⟩ : Sheaf J (Type u)) ⟶ ⟨Z.left, hZ⟩)) i)
  change (c.inj i).left ≫ d.hom = (f i).left at hd
  rw [← Category.assoc, hd, Over.w, Over.w]

private lemma SheafColimit.fac
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {T : Cᵒᵖ ⥤ Type u} {I : Type v} {A : I → Over T} {c : Cofan A}
    (hc : SheafColimit J c) (hT : Presheaf.IsSheaf J T)
    {Z : Over T} (hZ : Presheaf.IsSheaf J Z.left) (f : ∀ i, A i ⟶ Z) (i : I) :
    c.inj i ≫ hc.desc hT hZ f = f i :=
  Over.OverMorphism.ext <| congrArg (fun f => f.hom) (Cofan.IsColimit.fac hc.isColimit
    (fun i => (⟨(f i).left⟩ :
      (⟨(A i).left, hc.obj_isSheaf i⟩ : Sheaf J (Type u)) ⟶ ⟨Z.left, hZ⟩)) i)

/-- Two maps out of the vertex of a sheaf colimit agreeing on every summand are equal. -/
private lemma SheafColimit.hom_ext_left
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {T : Cᵒᵖ ⥤ Type u} {I : Type v} {A : I → Over T} {c : Cofan A}
    (hc : SheafColimit J c) {W : Cᵒᵖ ⥤ Type u} (hW : Presheaf.IsSheaf J W)
    {g h : c.pt.left ⟶ W} (hgh : ∀ i, (c.inj i).left ≫ g = (c.inj i).left ≫ h) : g = h :=
  congrArg (fun k : (⟨c.pt.left, hc.pt_isSheaf⟩ : Sheaf J (Type u)) ⟶ ⟨W, hW⟩ => k.hom)
    (Cofan.IsColimit.hom_ext hc.isColimit (⟨g⟩ : (⟨c.pt.left, hc.pt_isSheaf⟩ : Sheaf J (Type u)) ⟶
      ⟨W, hW⟩) ⟨h⟩ fun i => Sheaf.hom_ext (hgh i))

private lemma SheafColimit.hom_ext
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {T : Cᵒᵖ ⥤ Type u} {I : Type v} {A : I → Over T} {c : Cofan A}
    (hc : SheafColimit J c) {Z : Over T} (hZ : Presheaf.IsSheaf J Z.left)
    {f g : c.pt ⟶ Z} (hfg : ∀ i, c.inj i ≫ f = c.inj i ≫ g) : f = g :=
  Over.OverMorphism.ext (hc.hom_ext_left hZ fun i => congrArg (fun f => f.left) (hfg i))

private def sheafProductCofanIsColimit
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    [HasSheafify J (Type u)]
    {T : Cᵒᵖ ⥤ Type u} (hT : Presheaf.IsSheaf J T)
    {I K : Type v} {A : I → Over T} {B : K → Over T}
    {c : Cofan A} {d : Cofan B} (hc : SheafColimit J c) (hd : SheafColimit J d) :
    SheafColimit J (Cofan.mk (c.pt ⨯ d.pt)
      (fun p : I × K => prod.map (c.inj p.1) (d.inj p.2))) := by
  let prodSheaf (A B : Over T) (hA : Presheaf.IsSheaf J A.left)
      (hB : Presheaf.IsSheaf J B.left) : Sheaf J (Type u) :=
    ⟨(A ⨯ B).left, overProduct_isSheaf hT hA hB⟩
  have hp (A B : Over T) (hA : Presheaf.IsSheaf J A.left)
      (hB : Presheaf.IsSheaf J B.left) :
      IsPullback (C := Sheaf J (Type u))
        (⟨(prod.fst : A ⨯ B ⟶ A).left⟩ : prodSheaf A B hA hB ⟶ (⟨A.left, hA⟩ : Sheaf J (Type u)))
        (⟨(prod.snd : A ⨯ B ⟶ B).left⟩ : prodSheaf A B hA hB ⟶ (⟨B.left, hB⟩ : Sheaf J (Type u)))
        (⟨A.hom⟩ : (⟨A.left, hA⟩ : Sheaf J (Type u)) ⟶ (⟨T, hT⟩ : Sheaf J (Type u)))
        (⟨B.hom⟩ : (⟨B.left, hB⟩ : Sheaf J (Type u)) ⟶ (⟨T, hT⟩ : Sheaf J (Type u))) :=
    IsPullback.of_map_of_faithful (sheafToPresheaf J (Type u)) <|
      Over.isPullback_of_binaryFan_isLimit
        (BinaryFan.mk (prod.fst : A ⨯ B ⟶ A) (prod.snd : A ⨯ B ⟶ B)) (prodIsProd A B)
  refine ⟨fun p => overProduct_isSheaf hT (hc.obj_isSheaf p.1) (hd.obj_isSheaf p.2),
    overProduct_isSheaf hT hc.pt_isSheaf hd.pt_isSheaf, ?_⟩
  apply Nonempty.some
  refine (sheafCofan_universal _ hc.isColimit).nonempty_isColimit_prod_of_isPullback
    (sheafCofan_universal _ hd.isColimit)
    (fun i => (⟨(A i).hom⟩ :
      (⟨(A i).left, hc.obj_isSheaf i⟩ : Sheaf J (Type u)) ⟶ (⟨T, hT⟩ : Sheaf J (Type u))))
    (fun i => (⟨(B i).hom⟩ :
      (⟨(B i).left, hd.obj_isSheaf i⟩ : Sheaf J (Type u)) ⟶ (⟨T, hT⟩ : Sheaf J (Type u))))
    (⟨c.pt.hom⟩ : (⟨c.pt.left, hc.pt_isSheaf⟩ : Sheaf J (Type u)) ⟶ (⟨T, hT⟩ : Sheaf J (Type u)))
    (⟨d.pt.hom⟩ : (⟨d.pt.left, hd.pt_isSheaf⟩ : Sheaf J (Type u)) ⟶ (⟨T, hT⟩ : Sheaf J (Type u)))
    (fun i j => hp (A i) (B j) (hc.obj_isSheaf i) (hd.obj_isSheaf j))
    (hp c.pt d.pt hc.pt_isSheaf hd.pt_isSheaf) (Iso.refl _) ?_ ?_ ?_ ?_
  · exact fun i => Sheaf.hom_ext (Over.w _)
  · exact fun i => Sheaf.hom_ext (Over.w _)
  · intro i j; apply Sheaf.hom_ext
    simp only [Iso.refl_hom, Category.id_comp]
    change (prod.map (c.inj i) (d.inj j) ≫ prod.fst).left =
      (prod.fst ≫ c.inj i).left
    rw [prod.map_fst]
  · intro i j; apply Sheaf.hom_ext
    simp only [Iso.refl_hom, Category.id_comp]
    change (prod.map (c.inj i) (d.inj j) ≫ prod.snd).left =
      (prod.snd ≫ d.inj j).left
    rw [prod.map_snd]

variable {I : Type v}
  {X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (f : ∀ i, X i ⟶ T)
  (hT : IsAlgebraicSpace B S hS T)
  (hX : ∀ i, IsAlgebraicSpace B S hS (X i))

/-- Descent data whose objects admit an algebraic coproduct in sheaves. -/
public abbrev AlgebraicCoproductDescentData :=
  ObjectProperty.FullSubcategory
    (fun D : DescentData f hT hX =>
      Nonempty (AlgebraicSheafCoproduct (fun i => (D.obj i).left)
        D.obj_isAlgebraicSpace))

/-- A chosen sheaf coproduct of the objects of a descent datum. -/
public noncomputable def totalCoproduct (D : AlgebraicCoproductDescentData f hT hX) :
    AlgebraicSheafCoproduct (fun i => (D.obj.obj i).left)
      D.obj.obj_isAlgebraicSpace :=
  Classical.choice D.property

/-- The gluing isomorphism on the literal presheaf fibre products. -/
public abbrev gluingPullbackIso (D : DescentData f hT hX) (i j : I) :
    pullback ((D.obj i).hom ≫ f i) (f j) ≅
      pullback (f i) ((D.obj j).hom ≫ f j) :=
  (Over.prodLeftIsoPullback ((Over.map (f i)).obj (D.obj i)) (Over.mk (f j))).symm ≪≫
    (Over.forget T).mapIso ((Over.forget _).mapIso (D.gluing i j)) ≪≫
    Over.prodLeftIsoPullback (Over.mk (f i)) ((Over.map (f j)).obj (D.obj j))

section Construction

variable (Y : AlgebraicSheafCoproduct X hX)
  [HasSheafify (BigFppfOver.topology B S hS) (Type u)]

/-- Binary products in slices of presheaves, supplied directly: instance search for them times
out since Lean v4.35.0. -/
private local instance overPresheafHasBinaryProducts (T' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    HasBinaryProducts (Over T') :=
  Over.ConstructProducts.over_binaryProduct_of_pullback

private abbrev totalObj (D : AlgebraicCoproductDescentData f hT hX) : Over Y.sheaf.obj :=
  Over.mk ((totalCoproduct f hT hX D).map Y (fun i => (D.obj.obj i).hom))

private abbrev baseι (i : I) :
    Over.mk (f i) ⟶ Over.mk (Y.desc (spaceSheaf T hT) f) :=
  Over.homMk (Y.ι i).hom (Y.ι_desc _ _ _)

private abbrev totalι (D : AlgebraicCoproductDescentData f hT hX) (i : I) :
    (Over.map (f i)).obj (D.obj.obj i) ⟶
      (Over.map (Y.desc (spaceSheaf T hT) f)).obj (totalObj f hT hX Y D) :=
  Over.homMk ((totalCoproduct f hT hX D).ι i).hom (by
    change ((totalCoproduct f hT hX D).ι i).hom ≫
      (totalCoproduct f hT hX D).map Y (fun i => (D.obj.obj i).hom) ≫
        Y.desc (spaceSheaf T hT) f = (D.obj.obj i).hom ≫ f i
    rw [← Category.assoc, AlgebraicSheafCoproduct.ι_map, Category.assoc,
      AlgebraicSheafCoproduct.ι_desc])

private abbrev baseCofan := Cofan.mk _ (baseι f hT hX Y)

private abbrev totalCofan (D : AlgebraicCoproductDescentData f hT hX) :=
  Cofan.mk _ (totalι f hT hX Y D)

private def baseCofanIsColimit :
    SheafColimit (BigFppfOver.topology B S hS) (baseCofan f hT hX Y) :=
  ⟨fun i => (hX i).isSheaf, Y.sheaf.property, Y.isColimit⟩

private def totalCofanIsColimit (D : AlgebraicCoproductDescentData f hT hX) :
    SheafColimit (BigFppfOver.topology B S hS) (totalCofan f hT hX Y D) :=
  ⟨fun i => (D.obj.obj_isAlgebraicSpace i).isSheaf,
    (totalCoproduct f hT hX D).sheaf.property, (totalCoproduct f hT hX D).isColimit⟩

private abbrev sourceCofan (D : AlgebraicCoproductDescentData f hT hX) :=
  Cofan.mk ((Over.map (Y.desc (spaceSheaf T hT) f)).obj (totalObj f hT hX Y D) ⨯
    Over.mk (Y.desc (spaceSheaf T hT) f))
    (fun p : I × I => prod.map (totalι f hT hX Y D p.1) (baseι f hT hX Y p.2))

private abbrev targetCofan (D : AlgebraicCoproductDescentData f hT hX) :=
  Cofan.mk (Over.mk (Y.desc (spaceSheaf T hT) f) ⨯
    (Over.map (Y.desc (spaceSheaf T hT) f)).obj (totalObj f hT hX Y D))
    (fun p : I × I => prod.map (baseι f hT hX Y p.1) (totalι f hT hX Y D p.2))

private def sourceCofanIsColimit (D : AlgebraicCoproductDescentData f hT hX) :
    SheafColimit (BigFppfOver.topology B S hS) (sourceCofan f hT hX Y D) :=
  sheafProductCofanIsColimit hT.isSheaf
    (totalCofanIsColimit f hT hX Y D) (baseCofanIsColimit f hT hX Y)

private def targetCofanIsColimit (D : AlgebraicCoproductDescentData f hT hX) :
    SheafColimit (BigFppfOver.topology B S hS) (targetCofan f hT hX Y D) :=
  sheafProductCofanIsColimit hT.isSheaf
    (baseCofanIsColimit f hT hX Y) (totalCofanIsColimit f hT hX Y D)

private def totalGluing (D : AlgebraicCoproductDescentData f hT hX) :
    (sourceCofan f hT hX Y D).pt ≅ (targetCofan f hT hX Y D).pt where
  hom := (sourceCofanIsColimit f hT hX Y D).desc hT.isSheaf
    (targetCofanIsColimit f hT hX Y D).pt_isSheaf
    (fun p => (D.obj.gluing p.1 p.2).hom.left ≫ (targetCofan f hT hX Y D).inj p)
  inv := (targetCofanIsColimit f hT hX Y D).desc hT.isSheaf
    (sourceCofanIsColimit f hT hX Y D).pt_isSheaf
    (fun p => (D.obj.gluing p.1 p.2).inv.left ≫ (sourceCofan f hT hX Y D).inj p)
  hom_inv_id := by
    apply (sourceCofanIsColimit f hT hX Y D).hom_ext
      (sourceCofanIsColimit f hT hX Y D).pt_isSheaf
    intro p
    rw [← Category.assoc, SheafColimit.fac, Category.assoc, SheafColimit.fac]
    rw [← Category.assoc, ← Over.comp_left, Iso.hom_inv_id]
    simp
  inv_hom_id := by
    apply (targetCofanIsColimit f hT hX Y D).hom_ext
      (targetCofanIsColimit f hT hX Y D).pt_isSheaf
    intro p
    rw [← Category.assoc, SheafColimit.fac, Category.assoc, SheafColimit.fac]
    rw [← Category.assoc, ← Over.comp_left, Iso.inv_hom_id]
    simp

@[reassoc]
private lemma totalGluing_ι (D : AlgebraicCoproductDescentData f hT hX) (i j : I) :
    prod.map (totalι f hT hX Y D i) (baseι f hT hX Y j) ≫
      (totalGluing f hT hX Y D).hom =
    (D.obj.gluing i j).hom.left ≫
      prod.map (baseι f hT hX Y i) (totalι f hT hX Y D j) :=
  (sourceCofanIsColimit f hT hX Y D).fac hT.isSheaf
    (targetCofanIsColimit f hT hX Y D).pt_isSheaf _ (i, j)

omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
@[reassoc]
private lemma totalι_structure (D : AlgebraicCoproductDescentData f hT hX) (i : I) :
    totalι f hT hX Y D i ≫ structureMap (Y.desc (spaceSheaf T hT) f)
        (totalObj f hT hX Y D) =
      structureMap (f i) (D.obj.obj i) ≫ baseι f hT hX Y i :=
  Over.OverMorphism.ext (AlgebraicSheafCoproduct.ι_map _ _ _ _)

private def totalGluingOver (D : AlgebraicCoproductDescentData f hT hX) :
    Over.mk (prod.map
      (structureMap (Y.desc (spaceSheaf T hT) f) (totalObj f hT hX Y D))
      (𝟙 (Over.mk (Y.desc (spaceSheaf T hT) f)))) ≅
    Over.mk (prod.map (𝟙 (Over.mk (Y.desc (spaceSheaf T hT) f)))
      (structureMap (Y.desc (spaceSheaf T hT) f) (totalObj f hT hX Y D))) :=
  Over.isoMk (totalGluing f hT hX Y D) (by
    apply (sourceCofanIsColimit f hT hX Y D).hom_ext
      (overProduct_isSheaf hT.isSheaf Y.sheaf.property Y.sheaf.property)
    intro p
    dsimp only [sourceCofan, cofan_mk_inj, Over.mk_hom]
    rw [← Category.assoc, totalGluing_ι]
    apply prod.hom_ext
    · simp [Category.assoc, totalι_structure]
    · simp [Category.assoc, totalι_structure])

private lemma totalGluing_cocycle (D : AlgebraicCoproductDescentData f hT hX) :
    prod.map (totalGluing f hT hX Y D).hom (𝟙 _) ≫
        prodMapLastTwo (totalGluing f hT hX Y D).hom =
      prodMapFirstThird (totalGluing f hT hX Y D).hom := by
  apply (sheafProductCofanIsColimit hT.isSheaf
    (sourceCofanIsColimit f hT hX Y D) (baseCofanIsColimit f hT hX Y)).hom_ext
    (overProduct_isSheaf hT.isSheaf
      (overProduct_isSheaf hT.isSheaf Y.sheaf.property Y.sheaf.property)
      (totalCoproduct f hT hX D).sheaf.property)
  rintro ⟨⟨i, j⟩, k⟩
  dsimp only [cofan_mk_inj, sourceCofan, baseCofan]
  rw [← Category.assoc, prod.map_map, totalGluing_ι,
    show prod.map ((D.obj.gluing i j).hom.left ≫
      prod.map (baseι f hT hX Y i) (totalι f hT hX Y D j))
      (baseι f hT hX Y k ≫ 𝟙 _) =
    prod.map (D.obj.gluing i j).hom.left (𝟙 _) ≫
      prod.map (prod.map (baseι f hT hX Y i) (totalι f hT hX Y D j))
        (baseι f hT hX Y k) by simp]
  rw [Category.assoc,
    prodMapLastTwo_naturality (baseι f hT hX Y i) (totalι f hT hX Y D j)
      (baseι f hT hX Y k) (baseι f hT hX Y j) (totalι f hT hX Y D k)
      _ _ (totalGluing_ι f hT hX Y D j k)]
  rw [← Category.assoc, D.obj.cocycle]
  exact (prodMapFirstThird_naturality (totalι f hT hX Y D i) (baseι f hT hX Y j)
    (baseι f hT hX Y k) (baseι f hT hX Y i) (totalι f hT hX Y D k)
    _ _ (totalGluing_ι f hT hX Y D i k)).symm

private abbrev totalDescentData (D : AlgebraicCoproductDescentData f hT hX) :
    DescentData (fun _ : PUnit.{w + 1} => Y.desc (spaceSheaf T hT) f)
      hT (fun _ => Y.isAlgebraicSpace) where
  obj _ := totalObj f hT hX Y D
  obj_isAlgebraicSpace _ := (totalCoproduct f hT hX D).isAlgebraicSpace
  gluing _ _ := totalGluingOver f hT hX Y D
  cocycle _ _ _ := totalGluing_cocycle f hT hX Y D

private abbrev totalHom {D E : AlgebraicCoproductDescentData f hT hX}
    (α : ∀ i, D.obj.obj i ⟶ E.obj.obj i) :
    totalObj f hT hX Y D ⟶ totalObj f hT hX Y E :=
  Over.homMk ((totalCoproduct f hT hX D).map (totalCoproduct f hT hX E)
    (fun i => (α i).left)) (by
      dsimp only [totalObj, Over.mk_hom]
      rw [AlgebraicSheafCoproduct.map_comp]
      congr 1
      funext i
      exact Over.w (α i))

omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
@[reassoc]
private lemma totalHom_ι {D E : AlgebraicCoproductDescentData f hT hX}
    (α : ∀ i, D.obj.obj i ⟶ E.obj.obj i) (i : I) :
    totalι f hT hX Y D i ≫ (Over.map (Y.desc (spaceSheaf T hT) f)).map
        (totalHom f hT hX Y α) =
      (Over.map (f i)).map (α i) ≫ totalι f hT hX Y E i :=
  Over.OverMorphism.ext (AlgebraicSheafCoproduct.ι_map _ _ _ _)

private def totalMap {D E : AlgebraicCoproductDescentData f hT hX} (α : D ⟶ E) :
    totalDescentData.{u, v, w} f hT hX Y D ⟶ totalDescentData f hT hX Y E where
  hom _ := totalHom f hT hX Y α.hom.hom
  comm _ _ := by
    apply (sourceCofanIsColimit f hT hX Y D).hom_ext
      (targetCofanIsColimit f hT hX Y E).pt_isSheaf
    rintro ⟨i, j⟩
    change prod.map (totalι f hT hX Y D i) (baseι f hT hX Y j) ≫
      prod.map ((Over.map (Y.desc (spaceSheaf T hT) f)).map
        (totalHom f hT hX Y α.hom.hom)) (𝟙 _) ≫ (totalGluing f hT hX Y E).hom =
      prod.map (totalι f hT hX Y D i) (baseι f hT hX Y j) ≫
        (totalGluing f hT hX Y D).hom ≫ prod.map (𝟙 _)
          ((Over.map (Y.desc (spaceSheaf T hT) f)).map (totalHom f hT hX Y α.hom.hom))
    rw [← Category.assoc, prod.map_map, totalHom_ι,
      show prod.map ((Over.map (f i)).map (α.hom.hom i) ≫ totalι f hT hX Y E i)
          (baseι f hT hX Y j ≫ 𝟙 _) =
        prod.map ((Over.map (f i)).map (α.hom.hom i)) (𝟙 _) ≫
          prod.map (totalι f hT hX Y E i) (baseι f hT hX Y j) by simp,
      Category.assoc, totalGluing_ι, ← Category.assoc, α.hom.comm, totalGluing_ι_assoc]
    simp only [Category.assoc, prod.map_map, Category.id_comp, Category.comp_id, totalHom_ι]

private def totalFunctor :
    AlgebraicCoproductDescentData f hT hX ⥤
      DescentData (fun _ : PUnit.{w + 1} => Y.desc (spaceSheaf T hT) f)
        hT (fun _ => Y.isAlgebraicSpace) where
  obj := totalDescentData f hT hX Y
  map := totalMap f hT hX Y
  map_id _ := DescentData.Hom.ext <| funext fun _ =>
    Over.OverMorphism.ext <| AlgebraicSheafCoproduct.map_id _
  map_comp _ _ := DescentData.Hom.ext <| funext fun _ =>
    Over.OverMorphism.ext (AlgebraicSheafCoproduct.map_comp _ _ _ _ _).symm


private lemma coproduct_ι_mono (Z : AlgebraicSheafCoproduct X hX) (i : I) :
    Mono (Z.ι i).hom := by
  have : Mono (Z.ι i) := cofan_inj_mono _ Z.isColimit i
  exact (sheafToPresheaf _ (Type u)).map_mono (Z.ι i)

/-- The base summand inclusion over the coproduct is a monomorphism. -/
private lemma baseι_mono (i : I) : Mono (baseι f hT hX Y i) :=
  have := coproduct_ι_mono _ Y i
  Over.mono_of_mono_left _

/-- **A summand of a sheaf coproduct is the fibre product of a summand of the target along a
map of coproducts.** The square expressing that the `i`-th summand inclusion is the base
change of the `i`-th summand inclusion of the target along the coproduct of a family of
maps. -/
public lemma isPullback_coproduct_map
    {X' : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hX' : ∀ i, IsAlgebraicSpace B S hS (X' i)}
    (Z : AlgebraicSheafCoproduct X hX) (Z' : AlgebraicSheafCoproduct X' hX')
    (α : ∀ i, X i ⟶ X' i) (i : I) :
    IsPullback (Z.ι i).hom (α i) (Z.map Z' α) (Z'.ι i).hom :=
  (cofan_map_isPullback Z.isColimit Z'.isColimit
    (sheafCofan_universal _ Z.isColimit)
    (⟨Z.map Z' α⟩ : Z.sheaf ⟶ Z'.sheaf)
    (fun i => (⟨α i⟩ : spaceSheaf (X i) (hX i) ⟶ spaceSheaf (X' i) (hX' i)))
    (fun _ => Sheaf.hom_ext (AlgebraicSheafCoproduct.ι_map _ _ _ _)) i).map
      (sheafToPresheaf _ (Type u))

private def restrictTotalHom {D E : AlgebraicCoproductDescentData f hT hX}
    (β : totalObj f hT hX Y D ⟶ totalObj f hT hX Y E) (i : I) :
    D.obj.obj i ⟶ E.obj.obj i :=
  Over.homMk ((isPullback_coproduct_map _ (totalCoproduct f hT hX E) Y
    (fun i => (E.obj.obj i).hom) i).flip.lift
    (D.obj.obj i).hom (((totalCoproduct f hT hX D).ι i).hom ≫ β.left) (by
      rw [Category.assoc, show β.left ≫ (totalCoproduct f hT hX E).map Y
          (fun i => (E.obj.obj i).hom) =
        (totalCoproduct f hT hX D).map Y (fun i => (D.obj.obj i).hom) from Over.w β]
      exact (AlgebraicSheafCoproduct.ι_map (totalCoproduct f hT hX D) Y
        (fun i => (D.obj.obj i).hom) i).symm)) (by simp)

@[reassoc]
private lemma restrictTotalHom_ι {D E : AlgebraicCoproductDescentData f hT hX}
    (β : totalObj f hT hX Y D ⟶ totalObj f hT hX Y E) (i : I) :
    (restrictTotalHom f hT hX Y β i).left ≫ ((totalCoproduct f hT hX E).ι i).hom =
      ((totalCoproduct f hT hX D).ι i).hom ≫ β.left :=
  IsPullback.lift_snd _ _ _ _

private lemma totalHom_restrictTotalHom {D E : AlgebraicCoproductDescentData f hT hX}
    (β : totalObj f hT hX Y D ⟶ totalObj f hT hX Y E) :
    totalHom f hT hX Y (restrictTotalHom f hT hX Y β) = β := by
  apply Over.OverMorphism.ext
  refine AlgebraicSheafCoproduct.desc_ext _ (totalCoproduct f hT hX E).sheaf fun i => ?_
  change ((totalCoproduct f hT hX D).ι i).hom ≫
    (totalCoproduct f hT hX D).map (totalCoproduct f hT hX E)
      (fun i => (restrictTotalHom f hT hX Y β i).left) = _
  rw [AlgebraicSheafCoproduct.ι_map]
  exact restrictTotalHom_ι f hT hX Y β i

private lemma restrictTotalHom_totalHom {D E : AlgebraicCoproductDescentData f hT hX}
    (α : ∀ i, D.obj.obj i ⟶ E.obj.obj i) (i : I) :
    restrictTotalHom f hT hX Y (totalHom f hT hX Y α) i = α i := by
  apply Over.OverMorphism.ext
  have := coproduct_ι_mono _ (totalCoproduct f hT hX E) i
  apply (cancel_mono ((totalCoproduct f hT hX E).ι i).hom).mp
  rw [restrictTotalHom_ι]
  exact AlgebraicSheafCoproduct.ι_map _ _ _ _

private def restrictMap {D E : AlgebraicCoproductDescentData f hT hX}
    (β : totalDescentData.{u, v, w} f hT hX Y D ⟶ totalDescentData f hT hX Y E) :
    D ⟶ E := ObjectProperty.homMk
  { hom := restrictTotalHom f hT hX Y (β.hom PUnit.unit)
    comm := by
      intro i j
      have ht (k : I) :
          (Over.map (f k)).map (restrictTotalHom f hT hX Y (β.hom PUnit.unit) k) ≫
            totalι f hT hX Y E k =
          totalι f hT hX Y D k ≫ (Over.map (Y.desc (spaceSheaf T hT) f)).map
            (β.hom PUnit.unit) :=
        Over.OverMorphism.ext (restrictTotalHom_ι f hT hX Y (β.hom PUnit.unit) k)
      have hbi := baseι_mono f hT hX Y i
      have hti : Mono (totalι f hT hX Y E j) := by
        have := coproduct_ι_mono _ (totalCoproduct f hT hX E) j
        exact Over.mono_of_mono_left _
      apply (cancel_mono (prod.map (baseι f hT hX Y i) (totalι f hT hX Y E j))).mp
      have h := congrArg
        (fun t => prod.map (totalι f hT hX Y D i) (baseι f hT hX Y j) ≫ t)
        (β.comm PUnit.unit PUnit.unit)
      change prod.map (totalι f hT hX Y D i) (baseι f hT hX Y j) ≫
        (prod.map ((Over.map (Y.desc (spaceSheaf T hT) f)).map (β.hom PUnit.unit))
          (𝟙 _) ≫ (totalGluing f hT hX Y E).hom) =
        prod.map (totalι f hT hX Y D i) (baseι f hT hX Y j) ≫
          ((totalGluing f hT hX Y D).hom ≫ prod.map (𝟙 _)
            ((Over.map (Y.desc (spaceSheaf T hT) f)).map (β.hom PUnit.unit))) at h
      rw [← Category.assoc] at h
      simp only [prod.map_map] at h
      simp only [← ht i] at h
      simp only [Category.comp_id] at h
      rw [show prod.map
          ((Over.map (f i)).map (restrictTotalHom f hT hX Y (β.hom PUnit.unit) i) ≫
            totalι f hT hX Y E i) (baseι f hT hX Y j) =
        prod.map ((Over.map (f i)).map
          (restrictTotalHom f hT hX Y (β.hom PUnit.unit) i)) (𝟙 _) ≫
          prod.map (totalι f hT hX Y E i) (baseι f hT hX Y j) by simp] at h
      rw [Category.assoc, totalGluing_ι, totalGluing_ι_assoc] at h
      conv at h => rhs; rw [prod.map_map]
      simp only [← ht j] at h
      simpa only [Category.assoc, prod.map_map, Category.id_comp, Category.comp_id] using h }

private def totalFunctorFullyFaithful : (totalFunctor.{u, v, w} f hT hX Y).FullyFaithful where
  preimage := restrictMap f hT hX Y
  map_preimage β := DescentData.Hom.ext <| funext fun _ =>
    totalHom_restrictTotalHom f hT hX Y (β.hom PUnit.unit)
  preimage_map α := ObjectProperty.hom_ext _ <| DescentData.Hom.ext <| funext
    (restrictTotalHom_totalHom f hT hX Y α.hom.hom)


private abbrev restrictObject (E : DescentData (fun _ : PUnit.{w + 1} ↦ Y.desc (spaceSheaf T hT) f)
      hT (fun _ => Y.isAlgebraicSpace)) (i : I) :
    Over (X i) := (Over.pullback ((Y.ι i).hom)).obj (E.obj PUnit.unit)

private def restrictedObjectInclusion
    (E : DescentData (fun _ : PUnit.{w + 1} ↦ Y.desc (spaceSheaf T hT) f)
      hT (fun _ => Y.isAlgebraicSpace)) (i : I) :
  (Over.map (f i)).obj (restrictObject f hT hX Y E i) ⟶
      (Over.map (Y.desc (spaceSheaf T hT) f)).obj (E.obj PUnit.unit) :=
  Over.homMk (pullback.fst (E.obj PUnit.unit).hom ((Y.ι i).hom)) (by
    change pullback.fst (E.obj PUnit.unit).hom ((Y.ι i).hom) ≫
        (E.obj PUnit.unit).hom ≫ Y.desc (spaceSheaf T hT) f =
      pullback.snd (E.obj PUnit.unit).hom ((Y.ι i).hom) ≫ f i
    rw [← Category.assoc, pullback.condition]
    simp [Category.assoc])

omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
private lemma restrictedObject_isPullback
    (E : DescentData (fun _ : PUnit.{w + 1} ↦ Y.desc (spaceSheaf T hT) f)
      hT (fun _ => Y.isAlgebraicSpace)) (i : I) :
    IsPullback (restrictedObjectInclusion f hT hX Y E i)
      (structureMap (f i) (restrictObject f hT hX Y E i))
      (structureMap (Y.desc (spaceSheaf T hT) f) (E.obj PUnit.unit)) (baseι f hT hX Y i) := by
  let a := restrictedObjectInclusion f hT hX Y E i
  let b := structureMap (f i) (restrictObject f hT hX Y E i)
  let c := structureMap (Y.desc (spaceSheaf T hT) f) (E.obj PUnit.unit)
  let d := baseι f hT hX Y i
  let cone : PullbackCone c d := PullbackCone.mk a b (by
    apply Over.OverMorphism.ext
    simp [a, b, c, d, restrictedObjectInclusion, baseι, pullback.condition])
  apply IsPullback.of_isLimit (c := cone)
  refine PullbackCone.IsLimit.mk cone.condition (fun s ↦ ?_) ?_ ?_ ?_
  · have hs : s.fst.left ≫ (E.obj PUnit.unit).hom =
        s.snd.left ≫ (Y.ι i).hom := congrArg (fun t ↦ t.left) s.condition
    apply Over.homMk (pullback.lift s.fst.left s.snd.left hs) (by
      change pullback.lift s.fst.left s.snd.left _ ≫
        pullback.snd (E.obj PUnit.unit).hom ((Y.ι i).hom) ≫ f i = s.pt.hom
      rw [← Category.assoc, pullback.lift_snd]
      exact Over.w s.snd)
  · intro s
    apply Over.OverMorphism.ext
    simp only [cone, a, Over.comp_left, restrictedObjectInclusion]
    exact pullback.lift_fst _ _ _
  · intro s
    apply Over.OverMorphism.ext
    simp only [cone, b, PullbackCone.mk_snd, structureMap]
    exact pullback.lift_snd _ _ _
  · intro s m hm₁ hm₂
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · have hh := congrArg (fun t ↦ t.left) hm₁
      simp only [cone, a, restrictedObjectInclusion] at hh
      exact hh.trans (pullback.lift_fst _ _ _).symm
    · have hh := congrArg (fun t ↦ t.left) hm₂
      simp only [cone, b, PullbackCone.mk_snd, structureMap] at hh
      exact hh.trans (pullback.lift_snd _ _ _).symm

omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
private lemma restrictedSource_isPullback
    (E : DescentData (fun _ : PUnit.{w + 1} ↦ Y.desc (spaceSheaf T hT) f)
      hT (fun _ => Y.isAlgebraicSpace)) (i j : I) :
    IsPullback
      (prod.map (restrictedObjectInclusion f hT hX Y E i) (baseι f hT hX Y j))
      (prod.map (structureMap (f i) (restrictObject f hT hX Y E i)) (𝟙 (Over.mk (f j))))
      (prod.map (structureMap (Y.desc (spaceSheaf T hT) f) (E.obj PUnit.unit))
        (𝟙 (Over.mk (Y.desc (spaceSheaf T hT) f))))
      (prod.map (baseι f hT hX Y i) (baseι f hT hX Y j)) :=
  IsPullback.prod (restrictedObject_isPullback f hT hX Y E i) IsPullback.of_id_snd

omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
private lemma restrictedTarget_isPullback
    (E : DescentData (fun _ : PUnit.{w + 1} ↦ Y.desc (spaceSheaf T hT) f)
      hT (fun _ => Y.isAlgebraicSpace)) (i j : I) :
    IsPullback
      (prod.map (baseι f hT hX Y i) (restrictedObjectInclusion f hT hX Y E j))
      (prod.map (𝟙 (Over.mk (f i)))
        (structureMap (f j) (restrictObject f hT hX Y E j)))
      (prod.map (𝟙 (Over.mk (Y.desc (spaceSheaf T hT) f)))
        (structureMap (Y.desc (spaceSheaf T hT) f) (E.obj PUnit.unit)))
      (prod.map (baseι f hT hX Y i) (baseι f hT hX Y j)) :=
  IsPullback.prod IsPullback.of_id_snd (restrictedObject_isPullback f hT hX Y E j)

private def restrictedSourceComparison
    (E : DescentData (fun _ : PUnit.{w + 1} ↦ Y.desc (spaceSheaf T hT) f)
      hT (fun _ => Y.isAlgebraicSpace)) (i j : I) :
    Over.mk (prod.map (structureMap (f i) (restrictObject f hT hX Y E i))
      (𝟙 (Over.mk (f j)))) ≅
    (Over.pullback (prod.map (baseι f hT hX Y i) (baseι f hT hX Y j))).obj
      (Over.mk (prod.map (structureMap (Y.desc (spaceSheaf T hT) f) (E.obj PUnit.unit))
        (𝟙 (Over.mk (Y.desc (spaceSheaf T hT) f))))) := by
  let h := restrictedSource_isPullback f hT hX Y E i j
  exact Over.isoMk h.isoPullback h.isoPullback_hom_snd

private def restrictedTargetComparison
    (E : DescentData (fun _ : PUnit.{w + 1} ↦ Y.desc (spaceSheaf T hT) f)
      hT (fun _ => Y.isAlgebraicSpace)) (i j : I) :
    Over.mk (prod.map (𝟙 (Over.mk (f i)))
      (structureMap (f j) (restrictObject f hT hX Y E j))) ≅
    (Over.pullback (prod.map (baseι f hT hX Y i) (baseι f hT hX Y j))).obj
      (Over.mk (prod.map (𝟙 (Over.mk (Y.desc (spaceSheaf T hT) f)))
        (structureMap (Y.desc (spaceSheaf T hT) f) (E.obj PUnit.unit)))) := by
  let h := restrictedTarget_isPullback f hT hX Y E i j
  exact Over.isoMk h.isoPullback h.isoPullback_hom_snd

private def restrictedGluing
    (E : DescentData (fun _ : PUnit.{w + 1} ↦ Y.desc (spaceSheaf T hT) f)
      hT (fun _ => Y.isAlgebraicSpace)) (i j : I) :
    Over.mk (prod.map (structureMap (f i) (restrictObject f hT hX Y E i))
      (𝟙 (Over.mk (f j)))) ≅
    Over.mk (prod.map (𝟙 (Over.mk (f i)))
      (structureMap (f j) (restrictObject f hT hX Y E j))) :=
  restrictedSourceComparison f hT hX Y E i j ≪≫
    (Over.pullback (prod.map (baseι f hT hX Y i) (baseι f hT hX Y j))).mapIso
      (E.gluing PUnit.unit PUnit.unit) ≪≫
    (restrictedTargetComparison f hT hX Y E i j).symm

omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
@[reassoc]
private lemma restrictedGluing_naturality
    (E : DescentData (fun _ : PUnit.{w + 1} ↦ Y.desc (spaceSheaf T hT) f)
      hT (fun _ => Y.isAlgebraicSpace)) (i j : I) :
    prod.map (restrictedObjectInclusion f hT hX Y E i) (baseι f hT hX Y j) ≫
        (E.gluing PUnit.unit PUnit.unit).hom.left =
      (restrictedGluing f hT hX Y E i j).hom.left ≫
        prod.map (baseι f hT hX Y i) (restrictedObjectInclusion f hT hX Y E j) := by
  apply Over.OverMorphism.ext
  have hh := (restrictedSource_isPullback f hT hX Y E i j).isoPullback_hom_fst
  simp only [Over.mk_left, Over.comp_left, restrictedGluing, restrictedSourceComparison,
    restrictedTargetComparison, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Over.pullback_obj_left, Over.mk_hom, Over.isoMk_hom_left, Over.pullback_map_left,
    Over.isoMk_inv_left, Category.assoc, IsPullback.isoPullback_inv_fst]
  simp only [← Over.comp_left, pullback.lift_fst]
  exact (congrArg (fun t ↦ (t ≫ (E.gluing PUnit.unit PUnit.unit).hom.left).left) hh).symm

private lemma restrictedObjectInclusion_mono
    (E : DescentData (fun _ : PUnit.{w + 1} ↦ Y.desc (spaceSheaf T hT) f)
      hT (fun _ => Y.isAlgebraicSpace)) (i : I) :
    Mono (restrictedObjectInclusion f hT hX Y E i) := by
  have hfst : Mono (pullback.fst (E.obj PUnit.unit).hom ((Y.ι i).hom)) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _).flip (coproduct_ι_mono _ Y i)
  have hleft : Mono (restrictedObjectInclusion f hT hX Y E i).left := by
    simpa [restrictedObjectInclusion] using hfst
  let _ := hleft
  exact Over.mono_of_mono_left (restrictedObjectInclusion f hT hX Y E i)

private lemma restrictedCocycle
    (E : DescentData (fun _ : PUnit.{w + 1} ↦ Y.desc (spaceSheaf T hT) f)
      hT (fun _ => Y.isAlgebraicSpace)) (i j k : I) :
    prod.map (restrictedGluing f hT hX Y E i j).hom.left (𝟙 (Over.mk (f k))) ≫
        prodMapLastTwo (restrictedGluing f hT hX Y E j k).hom.left =
      prodMapFirstThird (restrictedGluing f hT hX Y E i k).hom.left := by
  let a := restrictedObjectInclusion f hT hX Y E i
  let b := restrictedObjectInclusion f hT hX Y E j
  let c := restrictedObjectInclusion f hT hX Y E k
  let ai := baseι f hT hX Y i
  let bj := baseι f hT hX Y j
  let ck := baseι f hT hX Y k
  let sourceIncl := prod.map (prod.map a bj) ck
  let targetIncl := prod.map (prod.map ai bj) c
  let middleIncl := prod.map (prod.map ai b) ck
  let localFirst := prod.map (restrictedGluing f hT hX Y E i j).hom.left
    (𝟙 (Over.mk (f k)))
  let globalFirst := prod.map (E.gluing PUnit.unit PUnit.unit).hom.left
    (𝟙 (Over.mk (Y.desc (spaceSheaf T hT) f)))
  let localTail := prodMapLastTwo (A := Over.mk (f i))
    (restrictedGluing f hT hX Y E j k).hom.left
  let globalTail := prodMapLastTwo (A := Over.mk (Y.desc (spaceSheaf T hT) f))
    (E.gluing PUnit.unit PUnit.unit).hom.left
  have hai := baseι_mono f hT hX Y i
  have hbj := baseι_mono f hT hX Y j
  have hc : Mono c := restrictedObjectInclusion_mono f hT hX Y E k
  have htarget : Mono targetIncl := by
    dsimp [targetIncl]
    infer_instance
  have hhead : localFirst ≫ middleIncl = sourceIncl ≫ globalFirst := by
    simp only [localFirst, middleIncl, sourceIncl, globalFirst, prod.map_map,
      Category.id_comp, Category.comp_id]
    rw [restrictedGluing_naturality f hT hX Y E i j]
  have htail : middleIncl ≫ globalTail = localTail ≫ targetIncl :=
    prodMapLastTwo_naturality ai b ck bj c _ _ (restrictedGluing_naturality f hT hX Y E j k)
  apply (cancel_mono targetIncl).mp
  calc
    (localFirst ≫ localTail) ≫ targetIncl =
        sourceIncl ≫ (globalFirst ≫ globalTail) := by
      rw [Category.assoc, ← htail, ← Category.assoc, hhead, Category.assoc]
    _ = sourceIncl ≫ prodMapFirstThird (E.gluing PUnit.unit PUnit.unit).hom.left := by
      rw [E.cocycle PUnit.unit PUnit.unit PUnit.unit]
    _ = prodMapFirstThird (restrictedGluing f hT hX Y E i k).hom.left ≫ targetIncl :=
      prodMapFirstThird_naturality a bj ck ai c _ _ (restrictedGluing_naturality f hT hX Y E i k)

private abbrev restrictedDescentData
    (E : DescentData (fun _ : PUnit.{w + 1} ↦ Y.desc (spaceSheaf T hT) f)
      hT (fun _ => Y.isAlgebraicSpace)) : DescentData f hT hX where
  obj i := restrictObject f hT hX Y E i
  obj_isAlgebraicSpace i := isAlgebraicSpace_pullback B S hS
    (E.obj PUnit.unit).hom (Y.ι i).hom (E.obj_isAlgebraicSpace PUnit.unit)
    (hX i) Y.isAlgebraicSpace
  gluing i j := restrictedGluing f hT hX Y E i j
  cocycle i j k := restrictedCocycle f hT hX Y E i j k


private abbrev restrictedCoproduct
    (E : DescentData (fun _ : PUnit.{w + 1} => Y.desc (spaceSheaf T hT) f)
      hT (fun _ => Y.isAlgebraicSpace)) :
    AlgebraicSheafCoproduct (fun i => (restrictObject f hT hX Y E i).left)
      (restrictedDescentData f hT hX Y E).obj_isAlgebraicSpace where
  sheaf := spaceSheaf (E.obj PUnit.unit).left (E.obj_isAlgebraicSpace PUnit.unit)
  ι i := ⟨pullback.fst (E.obj PUnit.unit).hom (Y.ι i).hom⟩
  exists_atlas := (E.obj_isAlgebraicSpace PUnit.unit).exists_atlas
  isColimit := by
    refine pullbackCofanIsColimit Y.ι Y.isColimit
      (H := fun i => spaceSheaf (restrictObject f hT hX Y E i).left
        ((restrictedDescentData f hT hX Y E).obj_isAlgebraicSpace i))
      (⟨(E.obj PUnit.unit).hom⟩ :
        spaceSheaf (E.obj PUnit.unit).left (E.obj_isAlgebraicSpace PUnit.unit) ⟶ Y.sheaf)
      (fun i => ⟨pullback.fst (E.obj PUnit.unit).hom (Y.ι i).hom⟩)
      (fun i => ⟨pullback.snd (E.obj PUnit.unit).hom (Y.ι i).hom⟩) fun i => ?_
    exact IsPullback.of_map_of_faithful (sheafToPresheaf _ (Type u))
      (IsPullback.of_hasPullback _ _)

private abbrev restrictedAlgebraicDescentData
    (E : DescentData (fun _ : PUnit.{w + 1} => Y.desc (spaceSheaf T hT) f)
      hT (fun _ => Y.isAlgebraicSpace)) : AlgebraicCoproductDescentData f hT hX :=
  ⟨restrictedDescentData f hT hX Y E, ⟨restrictedCoproduct f hT hX Y E⟩⟩

private def restrictedObjectSheafIso
    (E : DescentData (fun _ : PUnit.{w + 1} => Y.desc (spaceSheaf T hT) f)
      hT (fun _ => Y.isAlgebraicSpace)) :
    (totalCoproduct f hT hX (restrictedAlgebraicDescentData f hT hX Y E)).sheaf ≅
      (restrictedCoproduct f hT hX Y E).sheaf :=
  IsColimit.coconePointUniqueUpToIso
    (totalCoproduct f hT hX (restrictedAlgebraicDescentData f hT hX Y E)).isColimit
    (restrictedCoproduct f hT hX Y E).isColimit

@[reassoc]
private lemma restrictedObjectSheafIso_ι
    (E : DescentData (fun _ : PUnit.{w + 1} => Y.desc (spaceSheaf T hT) f)
      hT (fun _ => Y.isAlgebraicSpace)) (i : I) :
    ((totalCoproduct f hT hX (restrictedAlgebraicDescentData f hT hX Y E)).ι i).hom ≫
        (restrictedObjectSheafIso f hT hX Y E).hom.hom =
      pullback.fst (E.obj PUnit.unit).hom (Y.ι i).hom :=
  congrArg (fun k => k.hom)
    (IsColimit.comp_coconePointUniqueUpToIso_hom
      (totalCoproduct f hT hX (restrictedAlgebraicDescentData f hT hX Y E)).isColimit
      (restrictedCoproduct f hT hX Y E).isColimit ⟨i⟩)

private def restrictedObjectIso
    (E : DescentData (fun _ : PUnit.{w + 1} => Y.desc (spaceSheaf T hT) f)
      hT (fun _ => Y.isAlgebraicSpace)) :
    totalObj f hT hX Y (restrictedAlgebraicDescentData f hT hX Y E) ≅
      E.obj PUnit.unit :=
  Over.isoMk ((sheafToPresheaf _ (Type u)).mapIso
    (restrictedObjectSheafIso f hT hX Y E)) (by
      refine AlgebraicSheafCoproduct.desc_ext _ Y.sheaf fun i => ?_
      change ((totalCoproduct f hT hX (restrictedAlgebraicDescentData f hT hX Y E)).ι i).hom ≫
        (restrictedObjectSheafIso f hT hX Y E).hom.hom ≫ (E.obj PUnit.unit).hom =
        ((totalCoproduct f hT hX (restrictedAlgebraicDescentData f hT hX Y E)).ι i).hom ≫
          (totalCoproduct f hT hX (restrictedAlgebraicDescentData f hT hX Y E)).map Y
            (fun i => (restrictObject f hT hX Y E i).hom)
      rw [← Category.assoc, restrictedObjectSheafIso_ι, AlgebraicSheafCoproduct.ι_map]
      exact pullback.condition)

@[reassoc]
private lemma restrictedTotalObjectIso_ι
    (E : DescentData (fun _ : PUnit.{w + 1} => Y.desc (spaceSheaf T hT) f)
      hT (fun _ => Y.isAlgebraicSpace)) (i : I) :
    totalι f hT hX Y (restrictedAlgebraicDescentData f hT hX Y E) i ≫
        (Over.map (Y.desc (spaceSheaf T hT) f)).map (restrictedObjectIso f hT hX Y E).hom =
      restrictedObjectInclusion f hT hX Y E i :=
  Over.OverMorphism.ext (restrictedObjectSheafIso_ι f hT hX Y E i)

private def restrictedTotalIso
    (E : DescentData (fun _ : PUnit.{w + 1} => Y.desc (spaceSheaf T hT) f)
      hT (fun _ => Y.isAlgebraicSpace)) :
    totalDescentData f hT hX Y (restrictedAlgebraicDescentData f hT hX Y E) ≅ E :=
  DescentData.isoMk (fun _ => restrictedObjectIso f hT hX Y E) (by
    intro i j
    cases i
    cases j
    apply (sourceCofanIsColimit f hT hX Y
      (restrictedAlgebraicDescentData f hT hX Y E)).hom_ext
      (overProduct_isSheaf hT.isSheaf Y.sheaf.property
        (E.obj_isAlgebraicSpace PUnit.unit).isSheaf)
    rintro ⟨i', j'⟩
    dsimp only [sourceCofan, cofan_mk_inj, totalDescentData]
    rw [← Category.assoc, prod.map_map, restrictedTotalObjectIso_ι]
    simp only [Category.comp_id]
    rw [restrictedGluing_naturality f hT hX Y E i' j']
    simp only [totalGluingOver, Over.isoMk_hom_left]
    rw [totalGluing_ι_assoc]
    conv => rhs; rw [prod.map_map]
    simp only [Category.comp_id, restrictedTotalObjectIso_ι])

private theorem totalFunctor_essSurj : (totalFunctor.{u, v, w} f hT hX Y).EssSurj where
  mem_essImage E := ⟨restrictedAlgebraicDescentData f hT hX Y E, ⟨restrictedTotalIso f hT hX Y E⟩⟩

private lemma prodMap_left_fst {C : Type*} [Category* C] [HasPullbacks C]
    {T : C} [HasBinaryProducts (Over T)] {A B A' B' : Over T}
    (a : A ⟶ A') (b : B ⟶ B') :
    ((Over.prodLeftIsoPullback A B).inv ≫ (prod.map a b).left ≫
        (Over.prodLeftIsoPullback A' B').hom) ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ a.left := by
  simp only [Category.assoc, Over.prodLeftIsoPullback_hom_fst]
  rw [← Over.comp_left, prod.map_fst, Over.comp_left]
  simp

private lemma prodMap_left_snd {C : Type*} [Category* C] [HasPullbacks C]
    {T : C} [HasBinaryProducts (Over T)] {A B A' B' : Over T}
    (a : A ⟶ A') (b : B ⟶ B') :
    ((Over.prodLeftIsoPullback A B).inv ≫ (prod.map a b).left ≫
        (Over.prodLeftIsoPullback A' B').hom) ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ b.left := by
  simp only [Category.assoc, Over.prodLeftIsoPullback_hom_snd]
  rw [← Over.comp_left, prod.map_snd, Over.comp_left]
  simp

private abbrev totalSourceMap (D : AlgebraicCoproductDescentData f hT hX) (i j : I) :=
  (Over.prodLeftIsoPullback ((Over.map (f i)).obj (D.obj.obj i)) (Over.mk (f j))).inv ≫
    (prod.map (totalι f hT hX Y D i) (baseι f hT hX Y j)).left ≫
    (Over.prodLeftIsoPullback ((Over.map (Y.desc (spaceSheaf T hT) f)).obj
      (totalObj f hT hX Y D)) (Over.mk (Y.desc (spaceSheaf T hT) f))).hom

private abbrev totalTargetMap (D : AlgebraicCoproductDescentData f hT hX) (i j : I) :=
  (Over.prodLeftIsoPullback (Over.mk (f i)) ((Over.map (f j)).obj (D.obj.obj j))).inv ≫
    (prod.map (baseι f hT hX Y i) (totalι f hT hX Y D j)).left ≫
    (Over.prodLeftIsoPullback (Over.mk (Y.desc (spaceSheaf T hT) f))
      ((Over.map (Y.desc (spaceSheaf T hT) f)).obj (totalObj f hT hX Y D))).hom

private lemma totalGluingPullback_ι (D : AlgebraicCoproductDescentData f hT hX) (i j : I) :
    totalSourceMap f hT hX Y D i j ≫
        (gluingPullbackIso _ _ _ (totalDescentData.{u, v, w} f hT hX Y D)
          PUnit.unit PUnit.unit).hom =
      (gluingPullbackIso f hT hX D.obj i j).hom ≫ totalTargetMap f hT hX Y D i j := by
  have h := congrArg (fun t => t.left) (totalGluing_ι f hT hX Y D i j)
  dsimp only [Over.comp_left] at h
  simp only [gluingPullbackIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Over.forget_map, totalSourceMap, totalTargetMap,
    totalDescentData, totalGluingOver, Over.isoMk_hom_left,
    Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc (prod.map (totalι f hT hX Y D i) (baseι f hT hX Y j)).left, h]
  simp only [Category.assoc]

private lemma SheafColimit.conjugate_hom_ext
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {T : Cᵒᵖ ⥤ Type u} {I : Type v} {A : I → Over T} {c : Cofan A}
    (hc : SheafColimit J c) {Z : Cᵒᵖ ⥤ Type u} (e : c.pt.left ≅ Z)
    {Zi : I → Cᵒᵖ ⥤ Type u} (ei : ∀ i, (A i).left ≅ Zi i)
    {W : Cᵒᵖ ⥤ Type u} (hW : Presheaf.IsSheaf J W) {g h : Z ⟶ W}
    (hgh : ∀ i, (ei i).inv ≫ (c.inj i).left ≫ e.hom ≫ g =
      (ei i).inv ≫ (c.inj i).left ≫ e.hom ≫ h) : g = h := by
  apply (cancel_epi e.hom).mp
  exact hc.hom_ext_left hW fun i => (cancel_epi (ei i).inv).mp (hgh i)

end Construction


/-- The canonical equivalence, specified by its action on objects, gluing, and maps. -/
public structure FamilyCoproductEquivalence
    (Y : AlgebraicSheafCoproduct X hX) where
  /-- The equivalence of categories. -/
  equivalence :
    AlgebraicCoproductDescentData f hT hX ≌
      DescentData (fun _ : PUnit.{w + 1} => Y.desc (spaceSheaf T hT) f)
        hT (fun _ => Y.isAlgebraicSpace)
  /-- The object of the corresponding singleton descent datum is the sheaf coproduct. -/
  objIso (D : AlgebraicCoproductDescentData f hT hX) :
    (equivalence.functor.obj D).obj PUnit.unit ≅
      Over.mk ((totalCoproduct f hT hX D).map Y (fun i => (D.obj.obj i).hom))
  /-- Inclusion of a pairwise source fibre product into the coproduct fibre product. -/
  sourceMap (D : AlgebraicCoproductDescentData f hT hX) (i j : I) :
    pullback ((D.obj.obj i).hom ≫ f i) (f j) ⟶
      pullback
        (((equivalence.functor.obj D).obj PUnit.unit).hom ≫ Y.desc (spaceSheaf T hT) f)
        (Y.desc (spaceSheaf T hT) f)
  /-- The first source projection is the inclusion of the object summand. -/
  sourceMap_fst (D : AlgebraicCoproductDescentData f hT hX) (i j : I) :
    sourceMap D i j ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ ((totalCoproduct f hT hX D).ι i).hom ≫ (objIso D).inv.left
  /-- The second source projection is the inclusion of the base summand. -/
  sourceMap_snd (D : AlgebraicCoproductDescentData f hT hX) (i j : I) :
    sourceMap D i j ≫ pullback.snd _ _ = pullback.snd _ _ ≫ (Y.ι j).hom
  /-- The pairwise source fibre products cover the coproduct source fibre product: two
  maps to a sheaf agreeing on every summand are equal. This is the Stacks proof's
  observation that the fibre product of the coproducts is the coproduct of the pairwise
  fibre products, in the form that makes the gluing identification below a complete
  description of the resulting gluing isomorphism. -/
  sourceMap_jointly_epi (D : AlgebraicCoproductDescentData f hT hX)
    {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hW : Presheaf.IsSheaf (BigFppfOver.topology B S hS) W)
    {g h : pullback
        (((equivalence.functor.obj D).obj PUnit.unit).hom ≫ Y.desc (spaceSheaf T hT) f)
        (Y.desc (spaceSheaf T hT) f) ⟶ W}
    (hgh : ∀ i j, sourceMap D i j ≫ g = sourceMap D i j ≫ h) : g = h
  /-- Inclusion of a pairwise target fibre product into the coproduct fibre product. -/
  targetMap (D : AlgebraicCoproductDescentData f hT hX) (i j : I) :
    pullback (f i) ((D.obj.obj j).hom ≫ f j) ⟶
      pullback
        (Y.desc (spaceSheaf T hT) f)
        (((equivalence.functor.obj D).obj PUnit.unit).hom ≫ Y.desc (spaceSheaf T hT) f)
  /-- The first target projection is the inclusion of the base summand. -/
  targetMap_fst (D : AlgebraicCoproductDescentData f hT hX) (i j : I) :
    targetMap D i j ≫ pullback.fst _ _ = pullback.fst _ _ ≫ (Y.ι i).hom
  /-- The second target projection is the inclusion of the object summand. -/
  targetMap_snd (D : AlgebraicCoproductDescentData f hT hX) (i j : I) :
    targetMap D i j ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ ((totalCoproduct f hT hX D).ι j).hom ≫ (objIso D).inv.left
  /-- The pairwise target fibre products cover the coproduct target fibre product: two
  maps to a sheaf agreeing on every summand are equal. -/
  targetMap_jointly_epi (D : AlgebraicCoproductDescentData f hT hX)
    {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hW : Presheaf.IsSheaf (BigFppfOver.topology B S hS) W)
    {g h : pullback (Y.desc (spaceSheaf T hT) f)
        (((equivalence.functor.obj D).obj PUnit.unit).hom ≫ Y.desc (spaceSheaf T hT) f) ⟶ W}
    (hgh : ∀ i j, targetMap D i j ≫ g = targetMap D i j ≫ h) : g = h
  /-- The singleton gluing isomorphism restricts to the original one on each pair. -/
  gluing (D : AlgebraicCoproductDescentData f hT hX) (i j : I) :
    sourceMap D i j ≫
        (gluingPullbackIso _ _ _ (equivalence.functor.obj D) PUnit.unit PUnit.unit).hom =
      (gluingPullbackIso f hT hX D.obj i j).hom ≫ targetMap D i j
  /-- Maps of descent data are sent to sheaf coproducts of their component maps. -/
  map {D E : AlgebraicCoproductDescentData f hT hX} (α : D ⟶ E) :
    (objIso D).hom.left ≫
        (totalCoproduct f hT hX D).map (totalCoproduct f hT hX E)
          (fun i => (α.hom.hom i).left) =
      ((equivalence.functor.map α).hom PUnit.unit).left ≫ (objIso E).hom.left

private noncomputable def familyCoproductEquivalenceData
    (Y : AlgebraicSheafCoproduct X hX) :
    FamilyCoproductEquivalence.{u, v, w} f hT hX Y := by
  letI := BigFppfOver.hasSheafify_type B S hS
  letI : (totalFunctor.{u, v, w} f hT hX Y).EssSurj := totalFunctor_essSurj f hT hX Y
  let hff := totalFunctorFullyFaithful.{u, v, w} f hT hX Y
  letI : (totalFunctor.{u, v, w} f hT hX Y).Full := hff.full
  letI : (totalFunctor.{u, v, w} f hT hX Y).Faithful := hff.faithful
  letI : (totalFunctor.{u, v, w} f hT hX Y).IsEquivalence :=
    { faithful := inferInstance, full := inferInstance, essSurj := inferInstance }
  refine
    { equivalence := (totalFunctor f hT hX Y).asEquivalence
      objIso := fun _ => Iso.refl _
      sourceMap := totalSourceMap f hT hX Y
      sourceMap_fst := ?_
      sourceMap_snd := ?_
      sourceMap_jointly_epi := ?_
      targetMap := totalTargetMap f hT hX Y
      targetMap_fst := ?_
      targetMap_snd := ?_
      targetMap_jointly_epi := ?_
      gluing := totalGluingPullback_ι.{u, v, w} f hT hX Y
      map := ?_ }
  · intro D i j
    exact (prodMap_left_fst (totalι f hT hX Y D i) (baseι f hT hX Y j)).trans
      (congrArg (fun k => pullback.fst ((D.obj.obj i).hom ≫ f i) (f j) ≫ k)
        (Category.comp_id ((totalCoproduct f hT hX D).ι i).hom).symm)
  · exact fun D i j => prodMap_left_snd (totalι f hT hX Y D i) (baseι f hT hX Y j)
  · intro D W hW g h hgh
    dsimp only [Functor.asEquivalence, totalFunctor, totalDescentData] at g h hgh ⊢
    exact (sourceCofanIsColimit f hT hX Y D).conjugate_hom_ext
      (Over.prodLeftIsoPullback _ _)
      (fun p => Over.prodLeftIsoPullback _ _) hW (fun p => by
        simpa only [totalSourceMap, sourceCofan, cofan_mk_inj, Category.assoc] using hgh p.1 p.2)
  · exact fun D i j => prodMap_left_fst (baseι f hT hX Y i) (totalι f hT hX Y D j)
  · intro D i j
    exact (prodMap_left_snd (baseι f hT hX Y i) (totalι f hT hX Y D j)).trans
      (congrArg (fun k => pullback.snd (f i) ((D.obj.obj j).hom ≫ f j) ≫ k)
        (Category.comp_id ((totalCoproduct f hT hX D).ι j).hom).symm)
  · intro D W hW g h hgh
    dsimp only [Functor.asEquivalence, totalFunctor, totalDescentData] at g h hgh ⊢
    exact (targetCofanIsColimit f hT hX Y D).conjugate_hom_ext
      (Over.prodLeftIsoPullback _ _)
      (fun p => Over.prodLeftIsoPullback _ _) hW (fun p => by
        simpa only [totalTargetMap, targetCofan, cofan_mk_inj, Category.assoc] using hgh p.1 p.2)
  · intro D E α
    rfl


/-- The canonical equivalence between the descent data for a family whose objects have an
algebraic sheaf coproduct and the descent data relative to a given algebraic sheaf coproduct
`Y` of the sources. On the whole category of descent data, with `Y` the coproduct of the
sources in sheaves, this is
`AlgebraicGeometry.Space.Descent.familyCoproductEquivalenceOfAdmitsCoproductIndex`. -/
public noncomputable def familyCoproductEquivalence
    (Y : AlgebraicSheafCoproduct X hX) :
    FamilyCoproductEquivalence.{u, v, w} f hT hX Y :=
  Classical.choice (by exact ⟨familyCoproductEquivalenceData f hT hX Y⟩)

end AlgebraicGeometry.Space.Descent

end
