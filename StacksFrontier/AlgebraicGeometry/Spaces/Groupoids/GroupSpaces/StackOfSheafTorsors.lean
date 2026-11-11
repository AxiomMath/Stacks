module

public import StacksCore.CategoryTheory.FiberedInGroupoids
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.CategoryOfSheafTorsors
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Stack

/-!
# Torsors for a group object over a sheaf form a stack in groupoids

Let `S` be a scheme in a big fppf site, let `ℬ` be a sheaf on the big fppf site of `S` and let
`𝒢 ⟶ ℬ` be a map of sheaves carrying a group law over `ℬ`. Stacks 04UM asserts that the functor
`p : 𝒢/ℬ-Torsors ⥤ (Sch/S)_fppf` of Stacks 04UL
(`AlgebraicGeometry.Space.SheafTorsors.projection`) defines a stack in groupoids over the big
fppf site of `S`, that is, the three conditions of Stacks 02ZI: `p` is fibred in groupoids, the
presheaves `Isom(F, F')` on `(Sch/U)_fppf` are sheaves, and every descent datum along a covering
is effective.

Conditions (1) and (2) are proved here. The content of condition (1) is the restriction
`f^{-1}F` of a torsor along a morphism `f : V ⟶ U` of the site: the fibre product `F ×_U V`,
which carries the action of `V ×_{b ∘ f, ℬ} 𝒢` obtained by carrying the action of
`U ×_{b, ℬ} 𝒢` through the finite-product-preserving functor `(-) ×_U V` and identifying the
two descriptions of the acting group, is again a torsor, and the projection `F ×_U V ⟶ F` is a
morphism of `𝒢/ℬ-Torsors` over `f`. The fill-ins are unique because the total space of the
source of a morphism of `𝒢/ℬ-Torsors` is the fibre product of the total space of the target
with the new base.

The content of condition (2) is that a family of isomorphisms of the restrictions of two
objects along a covering family of `U` which agree on the overlaps glues to a single
isomorphism over `U`: the total space of a restriction is the base change of the total space,
so the total spaces of the restrictions along a covering family jointly cover every section of
the total space, and a map out of a sheaf prescribed on such a family, compatibly, exists and
is unique. The glued map of sheaves is then equivariant and cartesian over the identity of `U`
for the same reason, and its base morphism is forced, so it is a morphism of `𝒢/ℬ-Torsors`.

Condition (3), effectivity of descent data, is not proved here.

## Main results

* `AlgebraicGeometry.Space.SheafTorsors.existsUnique_hom_of_base`: a morphism of `𝒢/ℬ-Torsors`
  prescribed by a factorisation of its base morphism, that is the existence and uniqueness of
  fill-ins for `p`.
* `AlgebraicGeometry.Space.SheafTorsors.projection_isFiberedInGroupoids`: **Stacks 04UM**,
  condition (1) of Stacks 02ZI for `p : 𝒢/ℬ-Torsors ⥤ (Sch/S)_fppf`.
* `AlgebraicGeometry.Space.SheafTorsors.projection_isomIsSheaf`: **Stacks 04UM**, condition (2)
  of Stacks 02ZI for `p`, under the hypothesis that `ℬ` is a sheaf.

## Implementation notes

The acting group of the restricted torsor is `(Over.pullback (f ≫ b)).mapGrp.obj 𝒢`, while the
group whose action is carried along by the pullback functor is
`(Over.pullback f).mapGrp.obj ((Over.pullback b).mapGrp.obj 𝒢)`; these are canonically
isomorphic as group objects, by the comparison isomorphism
`CategoryTheory.Over.pullbackComp`, and `CategoryTheory.ModObj.ofIso` transports the action
across it. That a module object is carried along a lax monoidal functor at all is
`AlgebraicGeometry.Space.mapModObj`, and the shear map of the carried action is the image of the
original shear map up to the comparison isomorphisms, hence again an isomorphism.

Both the sheaf condition and the local existence of sections pass to the fibre product for
formal reasons: a fibre product of sheaves is a sheaf, the representable presheaves of the big
fppf site being sheaves by Stacks 025Z, and a base change of a locally surjective map of
presheaves is locally surjective.

Condition (2) needs the sheaf condition on `ℬ`, which the category of Stacks 04UL does not
carry, and only there: it is what forces the base morphism of the glued isomorphism, the
sections of `ℬ` over the members of the covering family agreeing on the overlaps. It is
therefore a hypothesis of `AlgebraicGeometry.Space.SheafTorsors.projection_isomIsSheaf` rather
than of the category.

## References

* [Stacks Project, Tag 04UM](https://stacks.math.columbia.edu/tag/04UM)
* [Stacks Project, Tag 02ZI](https://stacks.math.columbia.edu/tag/02ZI)
* [Stacks Project, Tag 04UL](https://stacks.math.columbia.edu/tag/04UL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory MonObj

universe u w u₁ v₁ u₂ w₁

namespace AlgebraicGeometry.Space

/-- A fibre product of sheaves of sets on a site is a sheaf. -/
private theorem isSheaf_pullback {D : Type u₁} [Category.{v₁} D] (J : GrothendieckTopology D)
    {F H K : Dᵒᵖ ⥤ Type u₂} (f : F ⟶ K) (g : H ⟶ K)
    (hF : Presheaf.IsSheaf J F) (hH : Presheaf.IsSheaf J H)
    (hK : Presheaf.IsSheaf J K) : Presheaf.IsSheaf J (pullback f g) := by
  apply ObjectProperty.prop_of_isLimit (Presheaf.IsSheaf J (A := Type u₂)) (pullback.isLimit f g)
  rintro (_ | _ | _) <;> assumption

/-- A base change of a locally surjective morphism of presheaves is locally surjective. -/
private theorem isLocallySurjective_of_isPullback {D : Type u₁} [Category.{v₁} D]
    (J : GrothendieckTopology D) {F H K L : Dᵒᵖ ⥤ Type u₂} {a : F ⟶ H} {b : F ⟶ K}
    {c : H ⟶ L} {d : K ⟶ L} (h : IsPullback a b c d)
    [Presheaf.IsLocallySurjective J c] : Presheaf.IsLocallySurjective J b := by
  constructor
  intro U s
  apply J.superset_covering _ (Presheaf.imageSieve_mem J c (d.app _ s))
  rintro V i ⟨t, ht⟩
  obtain ⟨x, -, hx⟩ := Types.exists_of_isPullback (h.map ((evaluation _ _).obj (Opposite.op V)))
    t (K.map i.op s)
    (ht.trans (d.naturality_apply i.op s).symm)
  exact ⟨x, hx⟩

/-- A lax monoidal functor carries an action of a monoid object on an object to an action of the
image monoid object on the image object. -/
@[instance_reducible]
private def mapModObj {E : Type u₁} [Category.{v₁} E] [MonoidalCategory E] {E' : Type u₂}
    [Category.{w₁} E'] [MonoidalCategory E'] (F : E ⥤ E') [F.LaxMonoidal] (R M : E) [MonObj R]
    [ModObj R M] :
    letI : MonObj (F.obj R) := F.monObjObj R
    ModObj (F.obj R) (F.obj M) := by
  letI : MonObj (F.obj R) := F.monObjObj R
  refine { smul := Functor.LaxMonoidal.μ F R M ≫ F.map (ModObj.smul (M := R) (X := M))
           one_smul := ?_
           mul_smul := ?_ }
  · dsimp [Functor.monObjObj]
    rw [MonoidalCategory.comp_whiskerRight]
    calc
      _ = Functor.LaxMonoidal.ε F ▷ F.obj M ≫
          (Functor.LaxMonoidal.μ F (𝟙_ E) M ≫
            F.map (MonObj.one (X := R) ▷ M)) ≫
              F.map (ModObj.smul (M := R) (X := M)) := by
        simpa only [Category.assoc] using congrArg
          (fun q => Functor.LaxMonoidal.ε F ▷ F.obj M ≫ q ≫
            F.map (ModObj.smul (M := R) (X := M)))
          (Functor.LaxMonoidal.μ_natural_left F (MonObj.one (X := R)) M)
      _ = (λ_ (F.obj M)).hom := by
        simp only [Category.assoc, ← F.map_comp]
        have hsource := ModObj.one_smul (M := R) M
        change MonObj.one (X := R) ▷ M ≫ ModObj.smul (M := R) (X := M) =
          (λ_ M).hom at hsource
        rw [hsource]
        exact (Functor.LaxMonoidal.left_unitality F M).symm
  · dsimp [Functor.monObjObj]
    simp only [MonoidalCategory.comp_whiskerRight, MonoidalCategory.whiskerLeft_comp,
      Category.assoc]
    slice_lhs 2 3 => rw [Functor.LaxMonoidal.μ_natural_left F (MonObj.mul (X := R)) M]
    simp only [Category.assoc, ← F.map_comp]
    have hsource := ModObj.mul_smul (M := R) M
    change MonObj.mul (X := R) ▷ M ≫ ModObj.smul (M := R) (X := M) =
      (α_ R R M).hom ≫ R ◁ ModObj.smul (M := R) (X := M) ≫
        ModObj.smul (M := R) (X := M) at hsource
    rw [hsource]
    simp only [F.map_comp]
    slice_lhs 1 3 => rw [Functor.LaxMonoidal.associativity F R R M]
    have hnat := Functor.LaxMonoidal.μ_natural_right F R (ModObj.smul (M := R) (X := M))
    change F.obj R ◁ F.map (ModObj.smul (M := R) (X := M)) ≫
      Functor.LaxMonoidal.μ F R M =
        Functor.LaxMonoidal.μ F R (R ⊗ M) ≫
          F.map (R ◁ ModObj.smul (M := R) (X := M)) at hnat
    slice_lhs 3 4 => rw [← hnat]
    simp only [Category.assoc]

/-- The shear map of an action carried along a monoidal functor between cartesian monoidal
categories is the image of the shear map, hence an isomorphism if the latter is. -/
private theorem mapModObj_isIso_leftSMul {E : Type u₁} [Category.{v₁} E]
    [CartesianMonoidalCategory E] {E' : Type u₂} [Category.{w₁} E'] [CartesianMonoidalCategory E']
    (F : E ⥤ E') [F.Monoidal] (R M : E) [MonObj R] [ModObj R M]
    [IsIso (ModObj.leftSMul R M)] :
    letI := F.monObjObj R
    letI := mapModObj F R M
    IsIso (ModObj.leftSMul (F.obj R) (F.obj M)) := by
  let _ := F.monObjObj R
  let _ := mapModObj F R M
  have h : ModObj.leftSMul (F.obj R) (F.obj M) =
      Functor.LaxMonoidal.μ F R M ≫ F.map (ModObj.leftSMul R M) ≫
        Functor.OplaxMonoidal.δ F M M := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [ModObj.leftSMul_fst, Category.assoc, Functor.OplaxMonoidal.δ_fst,
        ← F.map_comp, ModObj.leftSMul_fst]
      rfl
    · simp only [ModObj.leftSMul_snd, Category.assoc, Functor.OplaxMonoidal.δ_snd,
        ← F.map_comp, ModObj.leftSMul_snd, Functor.Monoidal.μ_snd]
  rw [h]
  infer_instance

/-- Transporting an action along an isomorphism of monoid objects preserves invertibility of the
shear map. -/
private theorem isIso_leftSMul_ofIso {E : Type u₁} [Category.{v₁} E]
    [CartesianMonoidalCategory E] {R R' M : E} [MonObj R] [MonObj R'] [ModObj R M]
    (e : R ≅ R') [IsMonHom e.hom] [IsIso (ModObj.leftSMul R M)] :
    letI := ModObj.ofIso e (Iso.refl M)
    IsIso (ModObj.leftSMul R' M) := by
  let _ := ModObj.ofIso e (Iso.refl M)
  have h : ModObj.leftSMul R' M = (e.inv ▷ M) ≫ ModObj.leftSMul R M := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [ModObj.leftSMul_fst, Category.assoc]
      change (e.inv ⊗ₘ 𝟙 M) ≫ γ[R, M] ≫ 𝟙 M = (e.inv ▷ M) ≫ γ[R, M]
      simp
    · simp
  rw [h]
  infer_instance

/-- The sieve of morphisms along which a given section of a presheaf becomes the image of a
section of one of a family of presheaves mapping to it. -/
@[sga "4 I 4.3.3" "more general"]
abbrev familyImageSieve
    {C : Type u₁} [Category.{v₁} C] {P : Cᵒᵖ ⥤ Type u₂}
    {I : Type w₁} {F : I → Cᵒᵖ ⥤ Type u₂} (π : ∀ i, F i ⟶ P)
    {W : C} (x : P.obj (Opposite.op W)) : Sieve W where
  arrows {Z} f := ∃ (i : I) (t : (F i).obj (Opposite.op Z)),
    (π i).app _ t = P.map f.op x
  downward_closed := by
    rintro Z Y f ⟨i, t, ht⟩ g
    refine ⟨i, (F i).map g.op t, ?_⟩
    rw [(π i).naturality_apply, ht]
    simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

/-- Two maps from a presheaf to a sheaf which agree on a family of presheaves over it whose
images cover every section are equal. -/
private theorem hom_ext_of_familyImageSieve
    {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
    {P Q : Cᵒᵖ ⥤ Type u₂} (hQ : Presheaf.IsSheaf J Q)
    {I : Type w₁} {F : I → Cᵒᵖ ⥤ Type u₂} (π : ∀ i, F i ⟶ P)
    (hπ : ∀ (W : C) (x : P.obj (Opposite.op W)), familyImageSieve π x ∈ J W)
    {g g' : P ⟶ Q} (h : ∀ i, π i ≫ g = π i ≫ g') : g = g' := by
  ext W x
  apply (hQ.isSheafFor _ (hπ W.unop x)).isSeparatedFor.ext
  rintro Z f ⟨i, t, ht⟩
  calc
    _ = g.app _ (P.map f.op x) := (g.naturality_apply f.op x).symm
    _ = g'.app _ (P.map f.op x) := by
      rw [← ht]
      exact congrArg (fun k : F i ⟶ Q => k.app _ t) (h i)
    _ = _ := g'.naturality_apply f.op x

/-- A map to a sheaf prescribed on a family of presheaves whose images cover every section and
whose prescribed maps agree wherever their images do. -/
private theorem exists_hom_of_familyImageSieve
    {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
    {P Q : Cᵒᵖ ⥤ Type u₂} (hQ : Presheaf.IsSheaf J Q)
    {I : Type w₁} {F : I → Cᵒᵖ ⥤ Type u₂} (π : ∀ i, F i ⟶ P)
    (hπ : ∀ (W : C) (x : P.obj (Opposite.op W)), familyImageSieve π x ∈ J W)
    (τ : ∀ i, F i ⟶ Q)
    (hτ : ∀ (W : C) (i j : I) (s : (F i).obj (Opposite.op W))
      (t : (F j).obj (Opposite.op W)), (π i).app _ s = (π j).app _ t →
        (τ i).app _ s = (τ j).app _ t) :
    ∃! g : P ⟶ Q, ∀ i, π i ≫ g = τ i := by
  classical
  let a {W : C} (x : P.obj (Opposite.op W)) :
      Presieve.FamilyOfElements Q (familyImageSieve π x).arrows :=
    fun Z f hf => (τ hf.choose).app _ hf.choose_spec.choose
  have ha {W Z : C} (x : P.obj (Opposite.op W)) (f : Z ⟶ W)
      (hf : familyImageSieve π x f) (i : I) (t : (F i).obj (Opposite.op Z))
      (ht : (π i).app _ t = P.map f.op x) : a x f hf = (τ i).app _ t :=
    hτ Z _ i _ t (hf.choose_spec.choose_spec.trans ht.symm)
  have ac {W : C} (x : P.obj (Opposite.op W)) : (a x).Compatible := by
    intro Z₁ Z₂ Z g₁ g₂ f₁ f₂ h₁ h₂ hw
    dsimp only [a]
    rw [← (τ h₁.choose).naturality_apply, ← (τ h₂.choose).naturality_apply]
    apply hτ
    rw [(π h₁.choose).naturality_apply, (π h₂.choose).naturality_apply,
      h₁.choose_spec.choose_spec, h₂.choose_spec.choose_spec]
    simp only [← ConcreteCategory.comp_apply, ← CategoryTheory.Functor.map_comp, ← op_comp, hw]
  let g {W : C} (x : P.obj (Opposite.op W)) :=
    (hQ.isSheafFor _ (hπ W x)).amalgamate (a x) (ac x)
  have hg {W Z : C} (x : P.obj (Opposite.op W)) (f : Z ⟶ W)
      (hf : familyImageSieve π x f) (i : I) (t : (F i).obj (Opposite.op Z))
      (ht : (π i).app _ t = P.map f.op x) :
      Q.map f.op (g x) = (τ i).app _ t :=
    ((hQ.isSheafFor _ (hπ W x)).isAmalgamation (ac x) f hf).trans (ha x f hf i t ht)
  have gn {W Z : C} (f : Z ⟶ W) (x : P.obj (Opposite.op W)) :
      Q.map f.op (g x) = g (P.map f.op x) := by
    apply (hQ.isSheafFor _ (hπ Z (P.map f.op x))).isSeparatedFor.ext
    rintro Y k ⟨i, t, ht⟩
    have ht' : (π i).app _ t = P.map (k ≫ f).op x := by
      simpa only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply] using ht
    rw [← ConcreteCategory.comp_apply, ← Q.map_comp, ← op_comp]
    exact (hg x (k ≫ f) ⟨i, t, ht'⟩ i t ht').trans
      (hg (P.map f.op x) k ⟨i, t, ht⟩ i t ht).symm
  let θ : P ⟶ Q :=
    { app := fun W => ↾(fun x => g x)
      naturality := by
        intro W Z f
        ext x
        exact (gn f.unop x).symm }
  have hθ (i : I) : π i ≫ θ = τ i := by
    ext W t
    simpa [θ] using hg ((π i).app W t) (𝟙 W.unop)
      (show familyImageSieve π ((π i).app W t) (𝟙 W.unop) from ⟨i, t, by simp⟩) i t (by simp)
  exact ⟨θ, hθ, fun θ' hθ' => hom_ext_of_familyImageSieve J hQ π hπ
    (fun i => (hθ' i).trans (hθ i).symm)⟩

/-- The base changes of a presheaf over `U` along a covering family of `U` cover every section
of that presheaf. -/
private theorem familyImageSieve_mem_of_isPullback
    {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
    {U : C} {P : Cᵒᵖ ⥤ Type v₁} (p : P ⟶ yoneda.obj U)
    {I : Type w₁} {V : I → C} (f : ∀ i, V i ⟶ U)
    (hf : Sieve.ofArrows V f ∈ J U)
    {F : I → Cᵒᵖ ⥤ Type v₁} (π : ∀ i, F i ⟶ P)
    (q : ∀ i, F i ⟶ yoneda.obj (V i))
    (h : ∀ i, IsPullback (π i) (q i) p (yoneda.map (f i)))
    (W : C) (x : P.obj (Opposite.op W)) : familyImageSieve π x ∈ J W := by
  apply J.superset_covering _ (J.pullback_stable (p.app _ x) hf)
  rintro Z g ⟨Y, k, l, ⟨i⟩, he⟩
  have hw : p.app _ (P.map g.op x) = (yoneda.map (f i)).app _ k := by
    rw [p.naturality_apply]
    exact he.symm
  obtain ⟨t, ht, -⟩ := Types.exists_of_isPullback
    ((h i).map ((evaluation _ _).obj (Opposite.op Z))) (P.map g.op x) k hw
  exact ⟨i, t, ht⟩


/-- Two sheaves receiving maps from a family of presheaves which cover every section of each and
induce the same relation on sections are isomorphic compatibly with those maps. -/
private theorem exists_iso_of_familyImageSieve
    {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
    {P Q : Cᵒᵖ ⥤ Type u₂} (hP : Presheaf.IsSheaf J P) (hQ : Presheaf.IsSheaf J Q)
    {I : Type w₁} {F : I → Cᵒᵖ ⥤ Type u₂}
    (π : ∀ i, F i ⟶ P) (τ : ∀ i, F i ⟶ Q)
    (hπ : ∀ (W : C) (x : P.obj (Opposite.op W)), familyImageSieve π x ∈ J W)
    (hτ : ∀ (W : C) (x : Q.obj (Opposite.op W)), familyImageSieve τ x ∈ J W)
    (hrel : ∀ (W : C) (i j : I) (s : (F i).obj (Opposite.op W))
      (t : (F j).obj (Opposite.op W)), (π i).app _ s = (π j).app _ t ↔
        (τ i).app _ s = (τ j).app _ t) :
    ∃ e : P ≅ Q, ∀ i, π i ≫ e.hom = τ i := by
  obtain ⟨g, hg, -⟩ := exists_hom_of_familyImageSieve J hQ π hπ τ
    (fun W i j s t => (hrel W i j s t).1)
  obtain ⟨g', hg', -⟩ := exists_hom_of_familyImageSieve J hP τ hτ π
    (fun W i j s t => (hrel W i j s t).2)
  refine ⟨⟨g, g', ?_, ?_⟩, hg⟩
  · apply hom_ext_of_familyImageSieve J hP π hπ
    intro i
    rw [← Category.assoc, hg, hg', Category.comp_id]
  · apply hom_ext_of_familyImageSieve J hQ τ hτ
    intro i
    rw [← Category.assoc, hg', hg, Category.comp_id]

/-- Two pullback squares on the same pair of projections cut out the same relation between the
elements of their two sides. -/
private theorem pullback_relation_iff
    {A X Y P Q : Type u₂} {a : A ⟶ X} {b : A ⟶ Y}
    {p : X ⟶ P} {q : Y ⟶ P} {p' : X ⟶ Q} {q' : Y ⟶ Q}
    (h : IsPullback a b p q) (h' : IsPullback a b p' q') (x : X) (y : Y) :
    p x = q y ↔ p' x = q' y := by
  constructor
  · intro e
    obtain ⟨z, rfl, rfl⟩ := Types.exists_of_isPullback h x y e
    exact congrArg (fun k : A ⟶ Q => k z) h'.w
  · intro e
    obtain ⟨z, rfl, rfl⟩ := Types.exists_of_isPullback h' x y e
    exact congrArg (fun k : A ⟶ P => k z) h.w

/-- Precomposing a family of maps with isomorphisms does not change the sieve of a section it
covers. -/
private theorem familyImageSieve_comp_iso
    {C : Type u₁} [Category.{v₁} C] {P : Cᵒᵖ ⥤ Type u₂}
    {I : Type w₁} {F F' : I → Cᵒᵖ ⥤ Type u₂} (e : ∀ i, F i ≅ F' i)
    (π : ∀ i, F' i ⟶ P) {W : C} (x : P.obj (Opposite.op W)) :
    familyImageSieve (fun i => (e i).hom ≫ π i) x = familyImageSieve π x := by
  ext Z f
  constructor
  · rintro ⟨i, t, ht⟩
    exact ⟨i, (e i).hom.app _ t, ht⟩
  · rintro ⟨i, t, ht⟩
    refine ⟨i, (e i).inv.app _ t, ?_⟩
    change (π i).app _ ((e i).hom.app _ ((e i).inv.app _ t)) = _
    simpa using ht

variable {𝒞 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝒞.Contains S}
  {B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u}

/-- Pulling `U ×_{b, ℬ} 𝒢` back along `f : V ⟶ U` gives the group obtained by pulling `𝒢` back
along the composite section `V ⟶ U ⟶ ℬ`, up to the associativity isomorphism of pullbacks. -/
private def sheafPullbackGroupCompIso (G : Grp (Over B))
    {U V : BigFppfOver 𝒞 S hS} (f : V ⟶ U) (b : yoneda.obj U ⟶ B) :
    sheafPullbackGroup G V (yoneda.map f ≫ b) ≅
      (Over.pullback (yoneda.map f)).mapGrp.obj (sheafPullbackGroup G U b) :=
  (Functor.mapGrpNatIso (Over.pullbackComp (yoneda.map f) b)).app G ≪≫
    (Functor.mapGrpCompIso (F := Over.pullback b)
      (G := Over.pullback (yoneda.map f))).app G

namespace SheafTorsors

/-- The action on an object of `𝒢/ℬ-Torsors` pulls back along a morphism of bases, after
identifying the pulled-back group with the group of the composite section. -/
@[instance_reducible]
private def pullbackAction (G : Grp (Over B)) {V : BigFppfOver 𝒞 S hS} (T : SheafTorsors G)
    (f : V ⟶ T.base) :
    ModObj (sheafPullbackGroup G V (yoneda.map f ≫ T.sec)).X
      ((Over.pullback (yoneda.map f)).obj T.total) := by
  let e := sheafPullbackGroupCompIso G f T.sec
  let eX : (sheafPullbackGroup G V (yoneda.map f ≫ T.sec)).X ≅
      ((Over.pullback (yoneda.map f)).mapGrp.obj (sheafPullbackGroup G T.base T.sec)).X :=
    (Grp.forget (Over (yoneda.obj V))).mapIso e
  letI : GrpObj (sheafPullbackGroup G T.base T.sec).X := (sheafPullbackGroup G T.base T.sec).grp
  letI : ModObj (sheafPullbackGroup G T.base T.sec).X T.total := T.action
  let G' := (Over.pullback (yoneda.map f)).mapGrp.obj (sheafPullbackGroup G T.base T.sec)
  letI : GrpObj G'.X := G'.grp
  letI : ModObj ((Over.pullback (yoneda.map f)).mapGrp.obj
      (sheafPullbackGroup G T.base T.sec)).X
      ((Over.pullback (yoneda.map f)).obj T.total) :=
    mapModObj (Over.pullback (yoneda.map f)) (sheafPullbackGroup G T.base T.sec).X T.total
  letI : IsMonHom eX.symm.hom := e.inv.hom.isMonHom_hom
  exact ModObj.ofIso eX.symm (Iso.refl _)

variable {G : Grp (Over B)}

/-- The pulled-back action on the restriction of a torsor along a morphism of bases has
invertible shear map. -/
private theorem pullbackAction_isPseudoTorsor (T : SheafTorsors G) {V : BigFppfOver 𝒞 S hS}
    (f : V ⟶ T.base) :
    letI := pullbackAction G T f
    AlgebraicGeometry.IsPseudoTorsor (sheafPullbackGroup G V (yoneda.map f ≫ T.sec)).X
      ((Over.pullback (yoneda.map f)).obj T.total) := by
  let _ : IsIso (ModObj.leftSMul T.group T.total) := T.isPseudoTorsor
  let G' := (Over.pullback (yoneda.map f)).mapGrp.obj (sheafPullbackGroup G T.base T.sec)
  let _ : GrpObj G'.X := G'.grp
  let _ : ModObj G'.X ((Over.pullback (yoneda.map f)).obj T.total) :=
    mapModObj (Over.pullback (yoneda.map f)) T.group T.total
  let _ : IsIso (ModObj.leftSMul G'.X ((Over.pullback (yoneda.map f)).obj T.total)) :=
    mapModObj_isIso_leftSMul (Over.pullback (yoneda.map f)) T.group T.total
  unfold pullbackAction
  let eX : (sheafPullbackGroup G V (yoneda.map f ≫ T.sec)).X ≅ G'.X :=
    (Grp.forget (Over (yoneda.obj V))).mapIso (sheafPullbackGroupCompIso G f T.sec)
  let _ : IsMonHom eX.symm.hom := (sheafPullbackGroupCompIso G f T.sec).inv.hom.isMonHom_hom
  exact isIso_leftSMul_ofIso eX.symm

/-- The restriction `(V, b ∘ f, f^{-1}F)` of an object of `𝒢/ℬ-Torsors` along a morphism
`f : V ⟶ U` of the big fppf site of `S`: the total space is the fibre product `F ×_U V`. -/
@[implicit_reducible]
private def pullbackTorsor (T : SheafTorsors G) {V : BigFppfOver 𝒞 S hS} (f : V ⟶ T.base) :
    SheafTorsors G where
  base := V
  sec := yoneda.map f ≫ T.sec
  total := (Over.pullback (yoneda.map f)).obj T.total
  action := pullbackAction G T f
  isTorsor := by
    refine ⟨?_, pullbackAction_isPseudoTorsor T f, ?_⟩
    · exact isSheaf_pullback _ T.total.hom (yoneda.map f) T.isSheaf
        (isAlgebraicSpace_yoneda 𝒞 S hS V).isSheaf
        (isAlgebraicSpace_yoneda 𝒞 S hS T.base).isSheaf
    · let _ := T.isLocallySurjective
      exact isLocallySurjective_of_isPullback _ (IsPullback.of_hasPullback _ _)

/-- The comparison isomorphism between the two descriptions of an iterated pullback does not
move the first projection. -/
private theorem pullbackComp_hom_app_fst_fst {D : Type u₁} [Category.{v₁} D] [HasPullbacks D]
    {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z) (A : Over Z) :
    ((Over.pullbackComp f g).hom.app A).left ≫
        pullback.fst (pullback.snd A.hom g) f ≫ pullback.fst A.hom g =
      pullback.fst A.hom (f ≫ g) := by
  have h := congrArg Over.Hom.left (conjugateEquiv_counit
    (Over.mapPullbackAdj (f ≫ g)) ((Over.mapPullbackAdj f).comp (Over.mapPullbackAdj g))
      (Over.mapComp f g).inv A)
  simp [Over.pullbackComp, conjugateIsoEquiv,
    Over.mapPullbackAdj_counit_app, Over.mapComp]

/-- The underlying map of the comparison isomorphism identifying the group of the composite
section with the pullback of the group. -/
private abbrev pullbackGroupComparison (T : SheafTorsors G) {V : BigFppfOver 𝒞 S hS}
    (f : V ⟶ T.base) :
    pullback G.X.hom (yoneda.map f ≫ T.sec) ⟶
      pullback (pullback.snd G.X.hom T.sec) (yoneda.map f) :=
  (sheafPullbackGroupCompIso G f T.sec).hom.hom.hom.left

/-- The comparison map of the groups is the comparison map of the iterated pullbacks. -/
private theorem pullbackGroupComparison_eq (T : SheafTorsors G) {V : BigFppfOver 𝒞 S hS}
    (f : V ⟶ T.base) :
    pullbackGroupComparison T f =
      ((Over.pullbackComp (yoneda.map f) T.sec).hom.app G.X).left := by
  change (((Over.pullbackComp (yoneda.map f) T.sec).hom.app G.X) ≫ 𝟙 _).left = _
  rw [Category.comp_id]

/-- Composing the comparison map of the groups with the projection to the group of the base
gives the base change map of the groups along `f`. -/
private theorem pullbackTorsor_groupComparison (T : SheafTorsors G) {V : BigFppfOver 𝒞 S hS}
    (f : V ⟶ T.base) :
    pullbackGroupComparison T f ≫
        pullback.fst (pullback.snd G.X.hom T.sec) (yoneda.map f) =
      groupBaseChange (T := pullbackTorsor T f) (T' := T) f rfl := by
  apply pullback.hom_ext
  · rw [Category.assoc, groupBaseChange_fst, pullbackGroupComparison_eq]
    exact pullbackComp_hom_app_fst_fst (yoneda.map f) T.sec G.X
  · have h := Over.w (sheafPullbackGroupCompIso G f T.sec).hom.hom.hom
    change pullbackGroupComparison T f ≫
      pullback.snd (pullback.snd G.X.hom T.sec) (yoneda.map f) =
      pullback.snd G.X.hom (yoneda.map f ≫ T.sec) at h
    rw [Category.assoc, pullback.condition, ← Category.assoc, h, groupBaseChange_snd]
    rfl

/-- The action morphism of an object of `𝒢/ℬ-Torsors`, as a map of presheaves. -/
private abbrev actionMap (T : SheafTorsors G) :
    pullback (pullback.snd G.X.hom T.sec) T.total.hom ⟶ T.total.left :=
  (γ[T.group, T.total]).left

/-- The projection `F ×_U V ⟶ F` is a morphism of `𝒢/ℬ-Torsors` from the restriction of
`(U, b, F)` along `f : V ⟶ U` to `(U, b, F)`, lying over `f`. -/
private def pullbackTorsorHom (T : SheafTorsors G) {V : BigFppfOver 𝒞 S hS} (f : V ⟶ T.base) :
    pullbackTorsor T f ⟶ T := by
  let F := Over.pullback (yoneda.map f)
  let e : (pullbackTorsor T f).group ⟶ F.obj T.group :=
    (sheafPullbackGroupCompIso G f T.sec).hom.hom.hom
  let comparison := Functor.LaxMonoidal.μ F T.group T.total
  have ha : actionMap (pullbackTorsor T f) =
      (e ▷ F.obj T.total).left ≫ comparison.left ≫ (F.map (γ[T.group, T.total])).left := by
    change (((e ⊗ₘ 𝟙 (F.obj T.total)) ≫
      (comparison ≫ F.map (γ[T.group, T.total]))) ≫ 𝟙 (F.obj T.total)).left = _
    simp only [Category.comp_id, MonoidalCategory.tensorHom_id, Over.comp_left]
  refine ⟨f, rfl, pullback.fst T.total.hom (yoneda.map f), IsPullback.of_hasPullback _ _, ?_⟩
  change actionMap (pullbackTorsor T f) ≫ _ = _
  have hm : (e ▷ F.obj T.total).left ≫ comparison.left ≫
        pullback.fst (T.group ⊗ T.total).hom (yoneda.map f) =
      actionBaseChange (T := pullbackTorsor T f) (T' := T) f rfl
        (pullback.fst T.total.hom (yoneda.map f)) pullback.condition.symm := by
    apply pullback.hom_ext
    · simp only [comparison, F, Category.assoc, Over.μ_pullback_left_fst_fst,
        Over.whiskerRight_left_fst_assoc]
      exact (congrArg
        (pullback.fst (pullbackTorsor T f).group.hom (F.obj T.total).hom ≫ ·)
        (pullbackTorsor_groupComparison T f)).trans
          (actionBaseChange_fst (T := pullbackTorsor T f) (T' := T) f rfl
            (pullback.fst T.total.hom (yoneda.map f)) pullback.condition.symm).symm
    · simp only [comparison, F, Category.assoc, Over.μ_pullback_left_fst_snd,
        Over.whiskerRight_left_snd_assoc]
      exact (actionBaseChange_snd (T := pullbackTorsor T f) (T' := T) f rfl
        (pullback.fst T.total.hom (yoneda.map f)) pullback.condition.symm).symm
  rw [ha]
  change ((e ▷ F.obj T.total).left ≫ comparison.left ≫
    (F.map (γ[T.group, T.total])).left) ≫ _ = _
  simp only [F, Over.pullback_map_left, Category.assoc, pullback.lift_fst]
  change (e ▷ F.obj T.total).left ≫ comparison.left ≫
      pullback.fst (T.group ⊗ T.total).hom (yoneda.map f) ≫ actionMap T =
    actionBaseChange (T := pullbackTorsor T f) (T' := T) f rfl
      (pullback.fst T.total.hom (yoneda.map f)) pullback.condition.symm ≫ actionMap T
  refine Eq.trans (Eq.symm ((Category.assoc _ _ _).trans
    (congrArg (fun k => (e ▷ F.obj T.total).left ≫ k) (Category.assoc _ _ _))))
    (congrArg (fun k => k ≫ actionMap T) hm)

/-- The morphism of total spaces of a morphism of `𝒢/ℬ-Torsors` lying over an isomorphism of the
big fppf site of `S` is an isomorphism. -/
private theorem isIso_map_of_isIso_base {T T' : SheafTorsors G} (φ : T ⟶ T')
    [IsIso (Hom.base φ)] : IsIso (Hom.map φ) := by
  have : IsIso (yoneda.map (Hom.base φ)) := Functor.map_isIso _ _
  exact (Hom.isPullback φ).isIso_fst_of_isIso

/-- The projection `F ×_U V ⟶ F` lies over `f : V ⟶ U`. -/
private theorem pullbackTorsorHom_base (T : SheafTorsors G) {V : BigFppfOver 𝒞 S hS}
    (f : V ⟶ T.base) : Hom.base (pullbackTorsorHom T f) = f :=
  rfl

/-- The action morphism of an object of `𝒢/ℬ-Torsors` lies over the base. -/
private theorem actionMap_comp_hom (T : SheafTorsors G) :
    actionMap T ≫ T.total.hom =
      pullback.snd (pullback.snd G.X.hom T.sec) T.total.hom ≫ T.total.hom :=
  (Over.w (γ[T.group, T.total])).trans pullback.condition

/-- **Stacks 04UM.** Existence and uniqueness of fill-ins for
`p : 𝒢/ℬ-Torsors ⥤ (Sch/S)_fppf`: given `φ : T' ⟶ T`, `ψ : T'' ⟶ T` and a factorisation
`f ∘ φ = ψ` of their base morphisms, there is a unique morphism `T'' ⟶ T'` over `f` composing
with `φ` to `ψ`. -/
theorem existsUnique_hom_of_base {T T' T'' : SheafTorsors G} (φ : T' ⟶ T) (ψ : T'' ⟶ T)
    (f : T''.base ⟶ T'.base) (hf : f ≫ Hom.base φ = Hom.base ψ) :
    ∃! χ : T'' ⟶ T', Hom.base χ = f ∧ χ ≫ φ = ψ := by
  have hb : yoneda.map f ≫ T'.sec = T''.sec := by
    rw [← Hom.comp_sec φ, ← Category.assoc, ← CategoryTheory.Functor.map_comp, hf,
      Hom.comp_sec ψ]
  have hw : Hom.map ψ ≫ T.total.hom =
      (T''.total.hom ≫ yoneda.map f) ≫ yoneda.map (Hom.base φ) := by
    rw [Category.assoc, ← CategoryTheory.Functor.map_comp, hf]
    exact (Hom.isPullback ψ).w
  let g := (Hom.isPullback φ).lift (Hom.map ψ) (T''.total.hom ≫ yoneda.map f) hw
  have hg : g ≫ Hom.map φ = Hom.map ψ := (Hom.isPullback φ).lift_fst _ _ _
  have hg' : g ≫ T'.total.hom = T''.total.hom ≫ yoneda.map f :=
    (Hom.isPullback φ).lift_snd _ _ _
  have hp : IsPullback g T''.total.hom T'.total.hom (yoneda.map f) := by
    apply IsPullback.of_right (h₁₂ := Hom.map φ) (h₂₂ := yoneda.map (Hom.base φ)) _ hg'
      (Hom.isPullback φ)
    simpa only [hg, ← CategoryTheory.Functor.map_comp, hf] using (Hom.isPullback ψ)
  have he : actionMap T'' ≫ g = actionBaseChange f hb g hg'.symm ≫ actionMap T' := by
    apply (Hom.isPullback φ).hom_ext
    · calc
        _ = actionMap T'' ≫ Hom.map ψ := by rw [Category.assoc, hg]
        _ = actionBaseChange (Hom.base ψ) (Hom.comp_sec ψ) (Hom.map ψ)
            (Hom.isPullback ψ).w.symm ≫ actionMap T := Hom.smul_comp ψ
        _ = (actionBaseChange f hb g hg'.symm ≫
              actionBaseChange (Hom.base φ) (Hom.comp_sec φ) (Hom.map φ)
                (Hom.isPullback φ).w.symm) ≫ actionMap T := by
          simp only [actionBaseChange_comp, hf, hg]
        _ = actionBaseChange f hb g hg'.symm ≫
            actionBaseChange (Hom.base φ) (Hom.comp_sec φ) (Hom.map φ)
              (Hom.isPullback φ).w.symm ≫ actionMap T := Category.assoc _ _ _
        _ = actionBaseChange f hb g hg'.symm ≫ actionMap T' ≫ Hom.map φ :=
          congrArg (fun k => actionBaseChange f hb g hg'.symm ≫ k) (Hom.smul_comp φ).symm
        _ = _ := (Category.assoc _ _ _).symm
    · calc
        _ = actionMap T'' ≫ T''.total.hom ≫ yoneda.map f := by rw [Category.assoc, hg']
        _ = pullback.snd (pullback.snd G.X.hom T''.sec) T''.total.hom ≫
            T''.total.hom ≫ yoneda.map f := by
          rw [← Category.assoc, actionMap_comp_hom, Category.assoc]
        _ = _ := by
          simp only [Category.assoc, actionMap_comp_hom, actionBaseChange_snd_assoc, hg']
  refine ⟨⟨f, hb, g, hp, he⟩, ⟨rfl, Hom.ext hf hg⟩, ?_⟩
  intro χ' hχ'
  refine Hom.ext hχ'.1 ((Hom.isPullback φ).hom_ext ?_ ?_)
  · exact (congrArg Hom.map hχ'.2).trans hg.symm
  · exact (Hom.isPullback χ').w.trans (by rw [hχ'.1, ← hg'])

variable (G)

/-- **Stacks 04UM.** Condition (1) of Stacks 02ZI for the functor
`p : 𝒢/ℬ-Torsors ⥤ (Sch/S)_fppf` of Stacks 04UL: `p` is fibred in groupoids. Every morphism
`f : V ⟶ U` of the big fppf site of `S` lifts to the restriction `(V, b ∘ f, f^{-1}F)` of an
object `(U, b, F)` along `f`, and fill-ins exist and are unique. -/
@[stacks 04UM "condition (1): p is fibred in groupoids"]
theorem projection_isFiberedInGroupoids : (projection G).IsFiberedInGroupoids where
  exists_lift := by
    rintro V U f T rfl
    refine ⟨pullbackTorsor T f, pullbackTorsorHom T f, ?_⟩
    rw [← pullbackTorsorHom_base T f]
    exact show (projection G).IsHomLift
      ((projection G).map (pullbackTorsorHom T f)) (pullbackTorsorHom T f) from inferInstance
  unique_lift := by
    intro T T' T'' φ ψ f hf
    exact existsUnique_hom_of_base φ ψ f hf

section IsomSheaf

/-- A family of base changes of a fibre product of presheaves covers every section of that fibre
product as soon as the family of base changes of its second factor does. -/
private theorem familyImageSieve_pullback_map_mem
    {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
    {A P R : Cᵒᵖ ⥤ Type u₂} (a : A ⟶ R) (p : P ⟶ R)
    {I : Type w₁} {A' P' R' : I → Cᵒᵖ ⥤ Type u₂}
    (a' : ∀ i, A' i ⟶ R' i) (p' : ∀ i, P' i ⟶ R' i)
    (α : ∀ i, A' i ⟶ A) (π : ∀ i, P' i ⟶ P) (ρ : ∀ i, R' i ⟶ R)
    (hA : ∀ i, IsPullback (α i) (a' i) a (ρ i))
    (hP : ∀ i, IsPullback (π i) (p' i) p (ρ i))
    (hπ : ∀ (W : C) (x : P.obj (Opposite.op W)), familyImageSieve π x ∈ J W)
    (W : C) (x : (pullback a p).obj (Opposite.op W)) :
    familyImageSieve (fun i => pullback.map (a' i) (p' i) a p (α i) (π i) (ρ i)
      (hA i).w.symm (hP i).w.symm) x ∈ J W := by
  apply J.superset_covering _ (hπ W ((pullback.snd a p).app _ x))
  rintro Z f ⟨i, t, ht⟩
  let E := (evaluation Cᵒᵖ (Type u₂)).obj (Opposite.op Z)
  let z := (pullback a p).map f.op x
  have hz : (pullback.snd a p).app _ z = (π i).app _ t :=
    ((pullback.snd a p).naturality_apply f.op x).trans ht.symm
  have hw : a.app _ ((pullback.fst a p).app _ z) = (ρ i).app _ ((p' i).app _ t) := by
    calc
      _ = p.app _ ((pullback.snd a p).app _ z) :=
        congrArg (fun k : pullback a p ⟶ R => k.app _ z) pullback.condition
      _ = p.app _ ((π i).app _ t) := congrArg (p.app _) hz
      _ = _ := congrArg (fun k : P' i ⟶ R => k.app _ t) (hP i).w
  obtain ⟨s, hs, hs'⟩ := Types.exists_of_isPullback ((hA i).map E)
    ((pullback.fst a p).app _ z) ((p' i).app _ t) hw
  obtain ⟨v, hv, hv'⟩ := Types.exists_of_isPullback
    ((IsPullback.of_hasPullback (a' i) (p' i)).map E) s t hs'
  change (α i).app (Opposite.op Z) s = (pullback.fst a p).app _ z at hs
  change (pullback.fst (a' i) (p' i)).app (Opposite.op Z) v = s at hv
  change (pullback.snd (a' i) (p' i)).app (Opposite.op Z) v = t at hv'
  refine ⟨i, v, ?_⟩
  apply Types.ext_of_isPullback ((IsPullback.of_hasPullback a p).map E)
  · have hmap : pullback.map (a' i) (p' i) a p (α i) (π i) (ρ i)
        (hA i).w.symm (hP i).w.symm ≫ pullback.fst a p =
        pullback.fst (a' i) (p' i) ≫ α i := pullback.lift_fst _ _ _
    exact (congrArg (fun k => k.app (Opposite.op Z) v) hmap).trans
      (by simpa only [NatTrans.comp_app, ConcreteCategory.comp_apply, hv] using hs)
  · have hmap : pullback.map (a' i) (p' i) a p (α i) (π i) (ρ i)
        (hA i).w.symm (hP i).w.symm ≫ pullback.snd a p =
        pullback.snd (a' i) (p' i) ≫ π i := pullback.lift_snd _ _ _
    exact (congrArg (fun k => k.app (Opposite.op Z) v) hmap).trans
      (by simpa only [NatTrans.comp_app, ConcreteCategory.comp_apply, hv'] using hz.symm)


/-- Two maps from a representable presheaf to a sheaf which agree on a covering family of the
representing object are equal. -/
private theorem yoneda_hom_ext_cover
    {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
    {Q : Cᵒᵖ ⥤ Type v₁} (hQ : Presheaf.IsSheaf J Q)
    {U : C} {I : Type w₁} {V : I → C} (f : ∀ i, V i ⟶ U)
    (hf : Sieve.ofArrows V f ∈ J U)
    {g g' : yoneda.obj U ⟶ Q} (h : ∀ i, yoneda.map (f i) ≫ g = yoneda.map (f i) ≫ g') :
    g = g' :=
  hom_ext_of_familyImageSieve J hQ (fun i => yoneda.map (f i))
    (familyImageSieve_mem_of_isPullback J (𝟙 (yoneda.obj U)) f hf
      (fun i => yoneda.map (f i)) (fun i => 𝟙 (yoneda.obj (V i)))
      (fun _ => IsPullback.id_vert _)) h

/-- The structure morphism of the total space of an object of `𝒢/ℬ-Torsors`, read as a map to a
prescribed object of the site equal to its base. -/
private abbrev normalizedProjection (T : SheafTorsors G)
    {U : BigFppfOver 𝒞 S hS} (hT : T.base = U) : T.total.left ⟶ yoneda.obj U :=
  T.total.hom ≫ yoneda.map (eqToHom (show T.base = U from hT))


/-- The morphism of total spaces of a morphism of `𝒢/ℬ-Torsors` identifies the source total space
with the base change of the target one, read over prescribed bases. -/
private theorem hom_normalized_isPullback {T T' : SheafTorsors G}
    {V U : BigFppfOver 𝒞 S hS} (hT : T.base = V) (hT' : T'.base = U)
    (φ : T ⟶ T') (f : V ⟶ U)
    (hf : Hom.base φ = eqToHom (show T.base = V from hT) ≫ f ≫
      eqToHom (show T'.base = U from hT').symm) :
    IsPullback φ.map (normalizedProjection G T hT) (normalizedProjection G T' hT')
      (yoneda.map f) := by
  subst hT hT'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hf
  simpa [normalizedProjection, hf] using φ.isPullback

/-- A morphism of `𝒢/ℬ-Torsors` lying over a morphism of the big fppf site of `S` has that
morphism as its morphism of bases. -/
private theorem hom_base_eq {T T' : SheafTorsors G} (φ : T ⟶ T')
    (f : T.base ⟶ T'.base)
    (h : (projection G).IsHomLift f φ) : Hom.base φ = f :=
  (@CategoryTheory.IsHomLift.eq_of_isHomLift _ _ _ _ (projection G) T T' f φ h).symm

/-- A fibre morphism of `𝒢/ℬ-Torsors` over an object of the site lies over an isomorphism. -/
private theorem isIso_base_of_fibreHom {T T' : SheafTorsors G} {U : BigFppfOver 𝒞 S hS}
    (hT : (projection G).obj T = U) (hT' : (projection G).obj T' = U) (φ : T ⟶ T')
    (h : Functor.FibreHom (projection G) T T' hT hT' φ) : IsIso (Hom.base φ) := by
  rw [hom_base_eq G φ _ h]
  exact IsIso.comp_isIso' (inferInstanceAs (IsIso (eqToHom (show T.base = U from hT))))
    (inferInstanceAs (IsIso (eqToHom (show T'.base = U from hT').symm)))

/-- The total space of a restriction of an object of `𝒢/ℬ-Torsors` along a morphism of the site is
the base change of the total space. -/
private theorem restriction_isPullback {U V : BigFppfOver 𝒞 S hS}
    (T : SheafTorsors G) (hT : T.base = U) (f : V ⟶ U)
    (r : Functor.Restriction (projection G) f T hT) :
    IsPullback r.hom.map (normalizedProjection G r.pt r.hpt)
      (normalizedProjection G T hT) (yoneda.map f) :=
  hom_normalized_isPullback G r.hpt hT r.hom f (hom_base_eq G r.hom _ r.isHomLift)

/-- The comparison morphism between two restrictions of an object of `𝒢/ℬ-Torsors` lies over the
morphism of the site relating them. -/
private theorem restriction_compTo_f {U V W : BigFppfOver 𝒞 S hS}
    (T : SheafTorsors G) (hT : T.base = U) (f : V ⟶ U) (k : W ⟶ V)
    {l : W ⟶ U} (hl : l = k ≫ f)
    (r : Functor.Restriction (projection G) f T hT)
    (s : Functor.Restriction (projection G) l T hT) :
    (Functor.Restriction.compTo (projection G) k f hl r s).base =
      eqToHom (show s.pt.base = W from s.hpt) ≫ k ≫
        eqToHom (show r.pt.base = V from r.hpt).symm := by
  have hlift : (projection G).IsHomLift
      (eqToHom s.hpt ≫ k ≫ eqToHom r.hpt.symm)
      (Functor.Restriction.compTo (projection G) k f hl r s) := by
    unfold Functor.Restriction.compTo
    infer_instance
  exact hom_base_eq G _ _ hlift

/-- The two comparison morphisms from a restriction over an overlap of a covering family to the
restrictions over the two members exhibit it as their fibre product. -/
private theorem restriction_overlap_isPullback
    {U V₁ V₂ W : BigFppfOver 𝒞 S hS}
    (T : SheafTorsors G) (hT : T.base = U) (f₁ : V₁ ⟶ U) (f₂ : V₂ ⟶ U)
    (p₁ : W ⟶ V₁) (p₂ : W ⟶ V₂) (hp : IsPullback p₁ p₂ f₁ f₂)
    (r₁ : Functor.Restriction (projection G) f₁ T hT)
    (r₂ : Functor.Restriction (projection G) f₂ T hT)
    (s : Functor.Restriction (projection G) (p₁ ≫ f₁) T hT) :
    IsPullback
      (Functor.Restriction.compTo (projection G) p₁ f₁ rfl r₁ s).map
      (Functor.Restriction.compTo (projection G) p₂ f₂ hp.w r₂ s).map
      r₁.hom.map r₂.hom.map := by
  let c₁ := Functor.Restriction.compTo (projection G) p₁ f₁ rfl r₁ s
  let c₂ := Functor.Restriction.compTo (projection G) p₂ f₂ hp.w r₂ s
  have hc₁ := hom_normalized_isPullback G s.hpt r₁.hpt c₁ p₁
    (restriction_compTo_f G T hT f₁ p₁ rfl r₁ s)
  have hc₂ := hom_normalized_isPullback G s.hpt r₂.hpt c₂ p₂
    (restriction_compTo_f G T hT f₂ p₂ hp.w r₂ s)
  have e₁ : c₁.map ≫ r₁.hom.map = s.hom.map :=
    congrArg Hom.map (Functor.Restriction.compTo_hom (projection G) p₁ f₁ rfl r₁ s)
  have e₂ : c₂.map ≫ r₂.hom.map = s.hom.map :=
    congrArg Hom.map (Functor.Restriction.compTo_hom (projection G) p₂ f₂ hp.w r₂ s)
  have outer := hc₁.paste_vert (hp.map yoneda)
  rw [← hc₂.w, ← (restriction_isPullback G T hT f₁ r₁).w] at outer
  exact IsPullback.of_bot outer (e₁.trans e₂.symm) (restriction_isPullback G T hT f₂ r₂)

/-- The total spaces of the restrictions of an object of `𝒢/ℬ-Torsors` along a covering family
cover every section of its total space. -/
private theorem restriction_familyImageSieve_mem
    {U : BigFppfOver 𝒞 S hS} (T : SheafTorsors G) (hT : T.base = U)
    {I : Type w} (V : I → BigFppfOver 𝒞 S hS) (f : ∀ i, V i ⟶ U)
    (hf : Sieve.ofArrows V f ∈ BigFppfOver.topology 𝒞 S hS U)
    (r : ∀ i, Functor.Restriction (projection G) (f i) T hT)
    (W : BigFppfOver 𝒞 S hS) (x : T.total.left.obj (Opposite.op W)) :
    familyImageSieve (fun i => (r i).hom.map) x ∈
      BigFppfOver.topology 𝒞 S hS W :=
  familyImageSieve_mem_of_isPullback _ (normalizedProjection G T hT) f hf
    (fun i => (r i).hom.map) (fun i => normalizedProjection G (r i).pt (r i).hpt)
    (fun i => restriction_isPullback G T hT (f i) (r i)) W x

/-- A family of isomorphisms between the restrictions of two objects of `𝒢/ℬ-Torsors` along a
covering family which agree on the overlaps glues to an isomorphism of their total spaces. -/
private theorem restriction_glue_iso
    {U : BigFppfOver 𝒞 S hS} (x y : SheafTorsors G)
    (hx : (projection G).obj x = U) (hy : (projection G).obj y = U)
    {I : Type w} (V : I → BigFppfOver 𝒞 S hS) (f : ∀ i, V i ⟶ U)
    (hf : Sieve.ofArrows V f ∈ BigFppfOver.topology 𝒞 S hS U)
    (Vij : I → I → BigFppfOver 𝒞 S hS)
    (pr₁ : ∀ i j, Vij i j ⟶ V i) (pr₂ : ∀ i j, Vij i j ⟶ V j)
    (hVij : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (f i) (f j))
    (xr : ∀ i, Functor.Restriction (projection G) (f i) x hx)
    (yr : ∀ i, Functor.Restriction (projection G) (f i) y hy)
    (xrij : ∀ i j, Functor.Restriction (projection G) (pr₁ i j ≫ f i) x hx)
    (yrij : ∀ i j, Functor.Restriction (projection G) (pr₁ i j ≫ f i) y hy)
    (φ : ∀ i, (xr i).pt ⟶ (yr i).pt)
    (hφ : ∀ i, Functor.FibreHom (projection G) (xr i).pt (yr i).pt
      (xr i).hpt (yr i).hpt (φ i))
    (hc : ∀ i j, ∃ (θ : (xrij i j).pt ⟶ (yrij i j).pt),
      Functor.FibreHom (projection G) (xrij i j).pt (yrij i j).pt
        (xrij i j).hpt (yrij i j).hpt θ ∧
      Functor.IsRestrictionOf (projection G) (pr₁ i j) rfl rfl
        (xr i) (yr i) (xrij i j) (yrij i j) (φ i) θ ∧
      Functor.IsRestrictionOf (projection G) (pr₂ i j) (hVij i j).w (hVij i j).w
        (xr j) (yr j) (xrij i j) (yrij i j) (φ j) θ) :
    ∃ e : x.total.left ≅ y.total.left,
      ∀ i, (xr i).hom.map ≫ e.hom = (φ i).map ≫ (yr i).hom.map := by
  have hi (i : I) : IsIso (Hom.map (φ i)) := by
    have := isIso_base_of_fibreHom G _ _ (φ i) (hφ i)
    exact isIso_map_of_isIso_base (φ i)
  apply exists_iso_of_familyImageSieve _ x.isSheaf y.isSheaf
    (fun i => (xr i).hom.map) (fun i => (φ i).map ≫ (yr i).hom.map)
    (restriction_familyImageSieve_mem G x hx V f hf xr)
  · intro W t
    exact Eq.mpr (congrArg (fun R => R ∈ BigFppfOver.topology 𝒞 S hS W)
      (familyImageSieve_comp_iso (fun i => asIso (φ i).map) (fun i => (yr i).hom.map) t))
      (restriction_familyImageSieve_mem G y hy V f hf yr W t)
  · intro W i j s t
    obtain ⟨θ, hθ, hθ₁, hθ₂⟩ := hc i j
    have := isIso_base_of_fibreHom G _ _ θ hθ
    have : IsIso (Hom.map θ) := isIso_map_of_isIso_base θ
    have px := restriction_overlap_isPullback G x hx (f i) (f j) (pr₁ i j) (pr₂ i j)
      (hVij i j) (xr i) (xr j) (xrij i j)
    have py := restriction_overlap_isPullback G y hy (f i) (f j) (pr₁ i j) (pr₂ i j)
      (hVij i j) (yr i) (yr j) (yrij i j)
    have py' : IsPullback
        (Functor.Restriction.compTo (projection G) (pr₁ i j) (f i) rfl
          (xr i) (xrij i j)).map
        (Functor.Restriction.compTo (projection G) (pr₂ i j) (f j) (hVij i j).w
          (xr j) (xrij i j)).map
        ((φ i).map ≫ (yr i).hom.map) ((φ j).map ≫ (yr j).hom.map) :=
      py.of_iso' (asIso (Hom.map θ)) (asIso (Hom.map (φ i))) (asIso (Hom.map (φ j)))
      (Iso.refl y.total.left) (congrArg Hom.map hθ₁) (congrArg Hom.map hθ₂)
      (by simp) (by simp)
    exact pullback_relation_iff
      (px.map ((evaluation _ _).obj (Opposite.op W)))
      (py'.map ((evaluation _ _).obj (Opposite.op W))) s t

/-- Base change of the acting group along a morphism of `𝒢/ℬ-Torsors` exhibits the acting group of
the source as the fibre product of that of the target with the source base. -/
private theorem groupBaseChange_isPullback {T T' : SheafTorsors G} (φ : T ⟶ T') :
    IsPullback (groupBaseChange (Hom.base φ) (Hom.comp_sec φ)) T.group.hom T'.group.hom
      (yoneda.map (Hom.base φ)) := by
  apply IsPullback.of_right (h₁₂ := pullback.fst G.X.hom T'.sec) (h₂₂ := T'.sec)
    _ (groupBaseChange_snd _ _) (IsPullback.of_hasPullback _ _)
  simpa only [groupBaseChange_fst, φ.comp_sec] using IsPullback.of_hasPullback G.X.hom T.sec

/-- The base change of the action along a morphism of `𝒢/ℬ-Torsors`. -/
private abbrev homActionBaseChange {T T' : SheafTorsors G} (φ : T ⟶ T') :=
  actionBaseChange φ.base φ.comp_sec φ.map φ.isPullback.w.symm

/-- The base changes of the action to the restrictions along a covering family cover every section
of the fibre product on which the acting group acts. -/
private theorem restriction_action_familyImageSieve_mem
    {U : BigFppfOver 𝒞 S hS} (T : SheafTorsors G) (hT : T.base = U)
    {I : Type w} (V : I → BigFppfOver 𝒞 S hS) (f : ∀ i, V i ⟶ U)
    (hf : Sieve.ofArrows V f ∈ BigFppfOver.topology 𝒞 S hS U)
    (r : ∀ i, Functor.Restriction (projection G) (f i) T hT)
    (W : BigFppfOver 𝒞 S hS)
    (s : (pullback T.group.hom T.total.hom).obj (Opposite.op W)) :
    familyImageSieve (fun i => homActionBaseChange G (r i).hom) s ∈
      BigFppfOver.topology 𝒞 S hS W :=
  familyImageSieve_pullback_map_mem _ T.group.hom T.total.hom
    (fun i => (r i).pt.group.hom) (fun i => (r i).pt.total.hom)
    (fun i => groupBaseChange (r i).hom.base (r i).hom.comp_sec) (fun i => (r i).hom.map)
    (fun i => yoneda.map (r i).hom.base) (fun i => groupBaseChange_isPullback G (r i).hom)
    (fun i => (r i).hom.isPullback) (restriction_familyImageSieve_mem G T hT V f hf r) W s

/-- The section of `ℬ` carried by an object of `𝒢/ℬ-Torsors`, read over a prescribed object of the
site equal to its base. -/
private abbrev normalizedSection (T : SheafTorsors G)
    {U : BigFppfOver 𝒞 S hS} (hT : T.base = U) : yoneda.obj U ⟶ B :=
  yoneda.map (eqToHom (show T.base = U from hT).symm) ≫ T.sec

/-- A morphism of `𝒢/ℬ-Torsors` is compatible with the sections of `ℬ`, read over prescribed
bases. -/
private theorem hom_normalized_comp_sec {T T' : SheafTorsors G}
    {V U : BigFppfOver 𝒞 S hS} (hT : T.base = V) (hT' : T'.base = U)
    (φ : T ⟶ T') (f : V ⟶ U)
    (hf : Hom.base φ = eqToHom (show T.base = V from hT) ≫ f ≫
      eqToHom (show T'.base = U from hT').symm) :
    yoneda.map f ≫ normalizedSection G T' hT' = normalizedSection G T hT := by
  subst hT hT'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hf
  simpa [normalizedSection, hf] using φ.comp_sec

/-- Base change of the action depends only on the two underlying morphisms. -/
private theorem actionBaseChange_congr {T T' : SheafTorsors G}
    {f f' : T.base ⟶ T'.base} {hf : yoneda.map f ≫ T'.sec = T.sec}
    {hf' : yoneda.map f' ≫ T'.sec = T.sec} {g g' : T.total.left ⟶ T'.total.left}
    {hg : T.total.hom ≫ yoneda.map f = g ≫ T'.total.hom}
    {hg' : T.total.hom ≫ yoneda.map f' = g' ≫ T'.total.hom}
    (hff : f = f') (hgg : g = g') :
    actionBaseChange f hf g hg = actionBaseChange f' hf' g' hg' := by
  subst hff hgg
  rfl

/-- An isomorphism of the total spaces of two objects of `𝒢/ℬ-Torsors` compatible with a family of
isomorphisms of their restrictions along a covering family is a morphism of `𝒢/ℬ-Torsors`. -/
private theorem restriction_glued_torsorHom
    (hB : Presheaf.IsSheaf (BigFppfOver.topology 𝒞 S hS) B)
    {U : BigFppfOver 𝒞 S hS} (x y : SheafTorsors G)
    (hx : (projection G).obj x = U) (hy : (projection G).obj y = U)
    (hxy : x.base = y.base)
    {I : Type w} (V : I → BigFppfOver 𝒞 S hS) (f : ∀ i, V i ⟶ U)
    (hf : Sieve.ofArrows V f ∈ BigFppfOver.topology 𝒞 S hS U)
    (xr : ∀ i, Functor.Restriction (projection G) (f i) x hx)
    (yr : ∀ i, Functor.Restriction (projection G) (f i) y hy)
    (φ : ∀ i, (xr i).pt ⟶ (yr i).pt)
    (hφ : ∀ i, Functor.FibreHom (projection G) (xr i).pt (yr i).pt
      (xr i).hpt (yr i).hpt (φ i))
    (e : x.total.left ≅ y.total.left)
    (he : ∀ i, (xr i).hom.map ≫ e.hom = (φ i).map ≫ (yr i).hom.map) :
    ∃ g : x ⟶ y, Hom.base g = eqToHom hxy ∧
      Hom.map g = e.hom ∧
      ∀ i, (xr i).hom ≫ g = φ i ≫ (yr i).hom := by
  have hφf (i : I) : Hom.base (φ i) =
      eqToHom (show (xr i).pt.base = V i from (xr i).hpt) ≫
        eqToHom (show (yr i).pt.base = V i from (yr i).hpt).symm :=
    hom_base_eq G (φ i) _ (hφ i)
  have hφf' (i : I) : Hom.base (φ i) =
      eqToHom (show (xr i).pt.base = V i from (xr i).hpt) ≫ 𝟙 (V i) ≫
        eqToHom (show (yr i).pt.base = V i from (yr i).hpt).symm := by
    rw [Category.id_comp]
    exact hφf i
  have hxf (i : I) : Hom.base (xr i).hom =
      eqToHom (show (xr i).pt.base = V i from (xr i).hpt) ≫ f i ≫
        eqToHom (show x.base = U from hx).symm :=
    hom_base_eq G (xr i).hom _ (xr i).isHomLift
  have hyf (i : I) : Hom.base (yr i).hom =
      eqToHom (show (yr i).pt.base = V i from (yr i).hpt) ≫ f i ≫
        eqToHom (show y.base = U from hy).symm :=
    hom_base_eq G (yr i).hom _ (yr i).isHomLift
  have hfac (i : I) : Hom.base (xr i).hom ≫ eqToHom hxy =
      Hom.base (φ i) ≫ Hom.base (yr i).hom := by
    rw [hxf i, hyf i, hφf i]
    simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
  have hb' : normalizedSection G x hx = normalizedSection G y hy := by
    apply yoneda_hom_ext_cover _ hB f hf
    intro i
    rw [hom_normalized_comp_sec G (xr i).hpt hx (xr i).hom (f i) (hxf i),
      hom_normalized_comp_sec G (yr i).hpt hy (yr i).hom (f i) (hyf i)]
    simpa using (hom_normalized_comp_sec G (xr i).hpt (yr i).hpt (φ i) (𝟙 (V i)) (hφf' i)).symm
  have hb : yoneda.map (eqToHom hxy) ≫ y.sec = x.sec :=
    calc yoneda.map (eqToHom hxy) ≫ y.sec
        = yoneda.map (eqToHom (show x.base = U from hx)) ≫
            yoneda.map (eqToHom (show y.base = U from hy).symm) ≫ y.sec := by
          rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, eqToHom_trans]
      _ = yoneda.map (eqToHom (show x.base = U from hx)) ≫ normalizedSection G y hy := rfl
      _ = yoneda.map (eqToHom (show x.base = U from hx)) ≫ normalizedSection G x hx := by rw [hb']
      _ = x.sec := by
          have hns : normalizedSection G x hx =
              yoneda.map (eqToHom (show x.base = U from hx).symm) ≫ x.sec := rfl
          rw [hns, ← Category.assoc, ← CategoryTheory.Functor.map_comp, eqToHom_trans,
            eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp]
  have hp : e.hom ≫ normalizedProjection G y hy = normalizedProjection G x hx := by
    apply hom_ext_of_familyImageSieve _ ((isAlgebraicSpace_yoneda 𝒞 S hS U).isSheaf)
      (fun i => (xr i).hom.map) (restriction_familyImageSieve_mem G x hx V f hf xr)
    intro i
    have hφp' : Hom.map (φ i) ≫ normalizedProjection G (yr i).pt (yr i).hpt =
        normalizedProjection G (xr i).pt (xr i).hpt := by
      rw [(hom_normalized_isPullback G (xr i).hpt (yr i).hpt (φ i) (𝟙 (V i)) (hφf' i)).w,
        CategoryTheory.Functor.map_id, Category.comp_id]
    rw [← Category.assoc, he, Category.assoc, (restriction_isPullback G y hy (f i) (yr i)).w,
      ← Category.assoc, hφp', ← (restriction_isPullback G x hx (f i) (xr i)).w]
  have hw : e.hom ≫ y.total.hom =
      x.total.hom ≫ yoneda.map (eqToHom hxy) := by
    apply (cancel_mono (yoneda.map (eqToHom (show y.base = U from hy)))).1
    calc (e.hom ≫ y.total.hom) ≫ yoneda.map (eqToHom (show y.base = U from hy))
        = e.hom ≫ normalizedProjection G y hy := Category.assoc _ _ _
      _ = normalizedProjection G x hx := hp
      _ = x.total.hom ≫ yoneda.map (eqToHom (show x.base = U from hx)) := rfl
      _ = (x.total.hom ≫ yoneda.map (eqToHom hxy)) ≫
            yoneda.map (eqToHom (show y.base = U from hy)) := by
          rw [Category.assoc, ← CategoryTheory.Functor.map_comp, eqToHom_trans]
  have hs : actionMap x ≫ e.hom =
      actionBaseChange (eqToHom hxy) hb e.hom hw.symm ≫ actionMap y := by
    apply hom_ext_of_familyImageSieve _ y.isSheaf
      (fun i => homActionBaseChange G (xr i).hom)
      (restriction_action_familyImageSieve_mem G x hx V f hf xr)
    intro i
    have h4 : homActionBaseChange G (xr i).hom ≫
          actionBaseChange (eqToHom hxy) hb e.hom hw.symm =
        homActionBaseChange G (φ i) ≫ homActionBaseChange G (yr i).hom := by
      dsimp only [homActionBaseChange]
      rw [actionBaseChange_comp, actionBaseChange_comp]
      exact actionBaseChange_congr G (hfac i) (he i)
    have hx' : actionMap (xr i).pt ≫ Hom.map (xr i).hom =
        homActionBaseChange G (xr i).hom ≫ actionMap x := Hom.smul_comp (xr i).hom
    have hφ' : actionMap (xr i).pt ≫ Hom.map (φ i) =
        homActionBaseChange G (φ i) ≫ actionMap (yr i).pt := Hom.smul_comp (φ i)
    have hy' : actionMap (yr i).pt ≫ Hom.map (yr i).hom =
        homActionBaseChange G (yr i).hom ≫ actionMap y := Hom.smul_comp (yr i).hom
    rw [reassoc_of% h4, ← reassoc_of% hx', he i, reassoc_of% hφ', hy']
  exact ⟨⟨eqToHom hxy, hb, e.hom, IsPullback.of_horiz_isIso ⟨hw⟩, hs⟩, rfl, rfl,
    fun i => Hom.ext (hfac i) (he i)⟩

/-- **Stacks 04UM.** Condition (2) of Stacks 02ZI for the functor
`p : 𝒢/ℬ-Torsors ⥤ (Sch/S)_fppf` of Stacks 04UL: for two objects `(U, b, F)` and `(U, b', F')`
over the same object of the big fppf site of `S`, the presheaf `Isom(F, F')` is a sheaf. A family
of isomorphisms of the restrictions along a covering family which agree on the overlaps glues,
uniquely, to an isomorphism over `U`, because the total spaces are sheaves and the restrictions
have as total spaces their base changes. -/
@[stacks 04UM "condition (2): the Isom presheaves are sheaves"]
theorem projection_isomIsSheaf
    (hB : Presheaf.IsSheaf (BigFppfOver.topology 𝒞 S hS) B) :
    ∀ {U : BigFppfOver 𝒞 S hS} (x y : SheafTorsors G)
      (hx : (projection G).obj x = U) (hy : (projection G).obj y = U)
      {I : Type w} (V : I → BigFppfOver 𝒞 S hS) (f : ∀ i, V i ⟶ U),
      Sieve.ofArrows V f ∈ BigFppfOver.topology 𝒞 S hS U →
      ∀ (Vij : I → I → BigFppfOver 𝒞 S hS)
        (pr₁ : ∀ i j, Vij i j ⟶ V i) (pr₂ : ∀ i j, Vij i j ⟶ V j)
        (hVij : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (f i) (f j))
        (xr : ∀ i, Functor.Restriction (projection G) (f i) x hx)
        (yr : ∀ i, Functor.Restriction (projection G) (f i) y hy)
        (xrij : ∀ i j, Functor.Restriction (projection G) (pr₁ i j ≫ f i) x hx)
        (yrij : ∀ i j, Functor.Restriction (projection G) (pr₁ i j ≫ f i) y hy),
        Functor.IsomIsSheafFor (projection G) x y hx hy V f Vij pr₁ pr₂ hVij xr yr xrij yrij := by
  intro U x y hx hy I V f hf Vij pr₁ pr₂ hVij xr yr xrij yrij φ hφ _ hc
  obtain ⟨e, he⟩ :=
    restriction_glue_iso G x y hx hy V f hf Vij pr₁ pr₂ hVij xr yr xrij yrij φ hφ hc
  have hxy : x.base = y.base := hx.trans hy.symm
  obtain ⟨g, hgf, hgg, hg⟩ :=
    restriction_glued_torsorHom G hB x y hx hy hxy V f hf xr yr φ hφ e he
  have hmap : eqToHom hx ≫ eqToHom hy.symm = (projection G).map g :=
    (eqToHom_trans hx hy.symm).trans hgf.symm
  have hgLift : Functor.FibreHom (projection G) x y hx hy g := by
    change (projection G).IsHomLift (eqToHom hx ≫ eqToHom hy.symm) g
    rw [hmap]
    exact CategoryTheory.IsHomLift.map _ _
  have hgi : IsIso g := by
    have := isIso_base_of_fibreHom G hx hy g hgLift
    exact isIso_of_isIso_base g
  refine ⟨g, ⟨hgLift, hgi, hg⟩, ?_⟩
  rintro k ⟨hk, -, hkg⟩
  have hkb : Hom.base k = eqToHom hx ≫ eqToHom hy.symm := hom_base_eq G k _ hk
  exact Hom.ext (hkb.trans hmap) (hom_ext_of_familyImageSieve _ y.isSheaf
    (fun i => (xr i).hom.map) (restriction_familyImageSieve_mem G x hx V f hf xr)
    fun i => congrArg Hom.map ((hkg i).trans (hg i).symm))

end IsomSheaf

end SheafTorsors

end AlgebraicGeometry.Space

end
