module

public import StacksFrontier.CategoryTheory.FiberedCategory.ProductProjection
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.AbelianDerivedExistence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.ProjectionDerivedLowerShriek
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.SimplicialModulesAbelian
import StacksCore.Tactic.StacksAttribute

/-!
# A sheaf on `Δ × C` is a simplicial sheaf on `C`, and `π_!` is the colimit over `Δᵒᵖ`

Let `(C, J)` be a site, let `π : Δ × C ⥤ C` be the second projection and let `Δ × C` carry the
topology inherited from `J` along `π` (Stacks 06NV; this is
`Stacks.SimplicialModules.projectionTopology C J` when `C` is small). Stacks 09D0 *identifies* a
sheaf on `Δ × C` with a simplicial sheaf on `C`. This file proves that identification as an
equivalence of categories, for coefficients in an arbitrary category `A`, and reads off the
description of the lower shriek of `π` that Stacks 09D0 asserts: `π_!` is the colimit over `Δᵒᵖ`.

The identification is levelwise restriction `F ↦ (n ↦ i_n^{-1}F)` along the fibre inclusions
`i_n : C ⥤ Δ × C`, `U ↦ (n, U)` (`CategoryTheory.Functor.prodSectionSnd`). That these
restrictions are again sheaves is the converse of
`CategoryTheory.Presheaf.isSheaf_inheritedTopology_prodSnd`, and it is the first thing proved
here. The inverse of the equivalence is uncurrying, exactly as for the sheaf of rings of
Stacks 09D1 (`Stacks.SimplicialModules.ringSheaf`), of which it is the coefficient-free form.

The payoff is the second half of Stacks 09D0. The equivalence `fibrewise`, the adjunction
`colim ⊣ const` on simplicial objects and the identification of the composite of restriction
along `π` with `fibrewise` as the constant simplicial sheaf together exhibit `fibrewise ⋙ colim`
as a left adjoint of restriction along `π`; the lower shriek `π_!` is another, and left adjoints
of one functor agree.

## Main definitions

* `Stacks.SimplicialModules.associatedPresheaf`: the presheaf on `Δ × C` obtained by uncurrying a
  simplicial sheaf on `C`, the coefficient-free form of
  `Stacks.SimplicialModules.associatedRingPresheaf`.
* `Stacks.SimplicialModules.fibrewise`: a sheaf on `Δ × C` read as a simplicial sheaf on `C`.
* `Stacks.SimplicialModules.sheafUncurry`: the inverse, uncurrying a simplicial sheaf on `C` into
  a sheaf on `Δ × C`.
* `Stacks.SimplicialModules.simplicialSheafEquivalence`: **Stacks 09D0**, the two are an
  equivalence of categories.

## Main results

* `CategoryTheory.Presheaf.isSheaf_prodSectionSnd_of_isSheaf_inheritedTopology`: a sheaf on
  `D × C` for the topology inherited from `(C, J)` along the second projection restricts to a
  `J`-sheaf on every slice `{d} × C`. This is the converse of
  `CategoryTheory.Presheaf.isSheaf_inheritedTopology_prodSnd`, and with it the sheaf condition on
  `Δ × C` is *exactly* the levelwise sheaf condition.
* `CategoryTheory.Prod.functorPullback_snd_mem_inheritedTopology`: the preimage of a covering
  sieve under the second projection is a covering sieve for the inherited topology.
* `Stacks.SimplicialModules.fibrewiseCompInverseImageIso`: `fibrewise` carries the inverse image
  of the projection to the constant simplicial sheaf.
* `Stacks.SimplicialModules.abelianLowerShriekIsoColim`: **Stacks 09D0**, `π_!` is the colimit
  over `Δᵒᵖ`.

## Implementation notes

The equivalence is built by hand rather than through `CategoryTheory.currying`: both round trips
are the identity on underlying data, so every component of the unit and the counit is
`CategoryTheory.Iso.refl`, and what has to be checked is only that these components are natural.
Going through currying would produce the same data wrapped in the equivalence
`(D × C)ᵒᵖ ≌ Dᵒᵖ × Cᵒᵖ` and would still leave the restriction to the full subcategories of
sheaves to be done by hand, because `CategoryTheory.SimplicialObject (Sheaf J A)` is not a full
subcategory of `SimplexCategoryᵒᵖ ⥤ Cᵒᵖ ⥤ A`. Uncurrying itself *is* taken from Mathlib
(`CategoryTheory.Functor.uncurry`), mirroring `Stacks.SimplicialModules.associatedRingPresheaf`.

All the naturality checks reduce to the single equation
`CategoryTheory.Functor.map_op_prod_fst_comp_snd`, which factors the restriction of a presheaf on
a product along `(φ, ψ)` as the restriction along `(φ, 𝟙)` followed by the restriction along
`(𝟙, ψ)`, together with its mirror image, `Stacks.SimplicialModules.associatedPresheaf_map` and
`CategoryTheory.Functor.map_id`.

The first two sections are stated for an arbitrary site `C` and arbitrary coefficients; the
abelian statements are stated for a small site, since that is where
`Stacks.SimplicialModules.projectionTopology` and the lower-shriek development live. No
hypothesis beyond continuity and cocontinuity of `π`, sheafification of abelian presheaves on
both sites, the existence of the right adjoint that `π_!` is defined from, and the colimits over
`Δᵒᵖ` that the statement names is used.

## References

* [Stacks Project, Tag 09D0](https://stacks.math.columbia.edu/tag/09D0)
* [Stacks Project, Tag 06NV](https://stacks.math.columbia.edu/tag/06NV), the inherited site.
* [Stacks Project, Tag 09D1](https://stacks.math.columbia.edu/tag/09D1), the same uncurrying for
  a simplicial sheaf of rings.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

open scoped CategoryTheory.Prod

universe w v u v₁ u₁ v₂ u₂ v₃ u₃ w₁

namespace CategoryTheory

section ProductSite

variable {A : Type u₁} [Category.{v₁} A] {D : Type u₂} [Category.{v₂} D] {C : Type u₃}
  [Category.{v₃} C]

/-- Restricting a presheaf along `h` is restricting along `g` and then along `f`, when
`f ≫ g = h`. -/
private lemma map_op_eq_comp_of_comp_eq (P : (D × C)ᵒᵖ ⥤ A) {X Y Z : D × C} {f : X ⟶ Y}
    {g : Y ⟶ Z} {h : X ⟶ Z} (e : f ≫ g = h) : P.map h.op = P.map g.op ≫ P.map f.op := by
  rw [← e, op_comp, P.map_comp]

/-- Restricting a presheaf on `D × C` along `(φ, ψ) : (d, U) ⟶ (d', V)` is restricting along
`(φ, 𝟙 V)` and then along `(𝟙 d, ψ)`: the two factorisations of `(φ, ψ)` through the two
"corners" `(d, V)` and `(d', U)` give this and
`CategoryTheory.Functor.map_op_prod_snd_comp_fst`. -/
lemma Functor.map_op_prod_fst_comp_snd (P : (D × C)ᵒᵖ ⥤ A) {d d' : D} (φ : d ⟶ d') {U V : C}
    (ψ : U ⟶ V) :
    P.map (φ ×ₘ ψ).op = P.map (φ ×ₘ 𝟙 V).op ≫ P.map (𝟙 d ×ₘ ψ).op := by
  exact map_op_eq_comp_of_comp_eq P (by ext <;> simp)

/-- Restricting a presheaf on `D × C` along `(φ, ψ) : (d, U) ⟶ (d', V)` is restricting along
`(𝟙 d', ψ)` and then along `(φ, 𝟙 U)`, the other factorisation of
`CategoryTheory.Functor.map_op_prod_fst_comp_snd`. -/
lemma Functor.map_op_prod_snd_comp_fst (P : (D × C)ᵒᵖ ⥤ A) {d d' : D} (φ : d ⟶ d') {U V : C}
    (ψ : U ⟶ V) :
    P.map (φ ×ₘ ψ).op = P.map (𝟙 d' ×ₘ ψ).op ≫ P.map (φ ×ₘ 𝟙 U).op := by
  exact map_op_eq_comp_of_comp_eq P (by ext <;> simp)

/-- Restricting a presheaf on `D × C` along a composition in the first coordinate. -/
lemma Functor.map_op_prod_comp_fst (P : (D × C)ᵒᵖ ⥤ A) {d d' d'' : D} (φ : d ⟶ d')
    (φ' : d' ⟶ d'') (U : C) :
    P.map ((φ ≫ φ') ×ₘ 𝟙 U).op = P.map (φ' ×ₘ 𝟙 U).op ≫ P.map (φ ×ₘ 𝟙 U).op := by
  exact map_op_eq_comp_of_comp_eq P (by ext <;> simp)

/-- Restricting a presheaf of types on `D × C` along a factored morphism, on elements: if
`a ≫ b = c` then the restriction of `z` along `c` is the restriction along `a` of its restriction
along `b`.

The inner restriction is a hypothesis rather than a subterm of the conclusion so that the lemma
applies to a given element. This is the shape the sheaf condition below needs, and it has to be
applied rather than rewritten with: the factorisations of an arrow of `D × C` through the
coordinate sections are composable only after unfolding
`CategoryTheory.Functor.prodSectionFst` and `CategoryTheory.Functor.prodSectionSnd`, so the
composites are not type-correct at the transparency `rw` uses. -/
lemma Functor.map_op_apply_comp (Q : (D × C)ᵒᵖ ⥤ Type w₁) {W X Z : D × C} {a : W ⟶ X}
    {b : X ⟶ Z} {c : W ⟶ Z} (h : a ≫ b = c) {z : Q.obj (op Z)} {u : Q.obj (op X)}
    (hu : Q.map b.op z = u) : Q.map c.op z = Q.map a.op u := by
  subst h
  subst hu
  exact Q.map_comp_apply b.op a.op z

/-- The preimage under the second projection of a covering sieve of `U` is a covering sieve of
`(d, U)` for the topology `D × C` inherits from `(C, J)` (Stacks 06NV).

It is generated by the covering family of Stacks 06NU consisting of the arrows
`(c, b) : (d', V) ⟶ (d, U)` with `c` invertible and `b` in the sieve: those are exactly the
strongly cartesian arrows lying over the sieve
(`CategoryTheory.Prod.isStronglyCartesian_snd_iff_isIso_fst`), their images are the arrows of the
sieve, and the sieve they generate is the preimage by
`CategoryTheory.Sieve.generate_eq_functorPullback_generate_map`. -/
theorem Prod.functorPullback_snd_mem_inheritedTopology (J : GrothendieckTopology C) (d : D)
    {U : C} {S : Sieve U} (hS : S ∈ J U) :
    Sieve.functorPullback (Prod.snd D C) (X := ((d, U) : D × C)) S ∈
      (Prod.snd D C).inheritedTopology J ((d, U) : D × C) := by
  have hcart : ∀ ⦃Y : D × C⦄ (g : Y ⟶ ((d, U) : D × C)), (S.arrows g.2 ∧ IsIso g.1) →
      (Prod.snd D C).IsStronglyCartesian ((Prod.snd D C).map g) g :=
    fun _ g hg => (Prod.isStronglyCartesian_snd_iff_isIso_fst g).2 hg.2
  have hmap : Presieve.map (Prod.snd D C)
      (fun ⦃Y : D × C⦄ (g : Y ⟶ ((d, U) : D × C)) => S.arrows g.2 ∧ IsIso g.1) = S.arrows := by
    refine le_antisymm (fun Z b hb => ?_) (fun Z b hb => ?_)
    · obtain ⟨hu⟩ := hb
      exact hu.1
    · exact Presieve.map_map (F := Prod.snd D C) (f := (𝟙 d ×ₘ b)) ⟨hb, inferInstance⟩
  have hgen : Sieve.generate
      (fun ⦃Y : D × C⦄ (g : Y ⟶ ((d, U) : D × C)) => S.arrows g.2 ∧ IsIso g.1)
      = Sieve.functorPullback (Prod.snd D C) (X := ((d, U) : D × C)) S := by
    rw [Sieve.generate_eq_functorPullback_generate_map (Prod.snd D C)
      (fun ⦃Y : D × C⦄ (g : Y ⟶ ((d, U) : D × C)) => S.arrows g.2 ∧ IsIso g.1) hcart, hmap,
      Sieve.generate_sieve]
  rw [← hgen, Functor.inheritedTopology_eq]
  refine Precoverage.generate_mem_toGrothendieck ⟨hcart, ?_⟩
  rw [GrothendieckTopology.mem_toPrecoverage_iff, hmap, Sieve.generate_sieve]
  exact hS

/-- A presheaf of types on `D × C` which is a sheaf for the preimage of a sieve `S` on `U` under
the second projection restricts to a sheaf for `S` on the slice `{d} × C`.

This is the converse of `CategoryTheory.Presieve.isSheafFor_functorPullback_snd`. A compatible
family `y` for `S` on the restricted presheaf is spread over the whole preimage of `S` by
`x (c, b) := Q(c, 𝟙)(y b)`, and the two sheaf conditions have the same amalgamations because
every arrow `g` of `D × C` into `(d, U)` factors as `(g.1, 𝟙) ≫ (𝟙 d, g.2)`. -/
theorem Presieve.isSheafFor_prodSectionSnd_of_isSheafFor_functorPullback_snd
    (Q : (D × C)ᵒᵖ ⥤ Type w₁) (d : D) {U : C} (S : Sieve U)
    (hS : Presieve.IsSheafFor Q
      (Sieve.functorPullback (Prod.snd D C) (X := ((d, U) : D × C)) S).arrows) :
    Presieve.IsSheafFor ((Functor.prodSectionSnd d).op ⋙ Q) S.arrows := by
  intro y hy
  have hys := hy.to_sieveCompatible
  have hfac : ∀ {Y : D × C} (g : Y ⟶ ((d, U) : D × C)),
      (Functor.prodSectionFst Y.2).map g.1 ≫ (Functor.prodSectionSnd d).map g.2 = g :=
    fun g => Prod.ext (Category.comp_id _) (Category.id_comp _)
  have hcomp : Presieve.FamilyOfElements.Compatible (P := Q)
      (R := (Sieve.functorPullback (Prod.snd D C) (X := ((d, U) : D × C)) S).arrows)
      (fun Y g hg => Q.map ((Functor.prodSectionFst Y.2).map g.1).op (y g.2 hg)) := by
    refine (Presieve.compatible_iff_sieveCompatible _).2 ?_
    intro Y Z g f hg
    have h1 : (Functor.prodSectionFst Z.2).map (f ≫ g).1 ≫ (Functor.prodSectionSnd d).map f.2
        = f ≫ (Functor.prodSectionFst Y.2).map g.1 :=
      Prod.ext (Category.comp_id _) ((Category.id_comp f.2).trans (Category.comp_id f.2).symm)
    exact (Functor.map_op_apply_comp Q h1 (hys g.2 f.2 hg).symm).symm.trans
      (Functor.map_op_apply_comp Q (a := f) (b := (Functor.prodSectionFst Y.2).map g.1)
        (z := y g.2 hg) rfl rfl)
  obtain ⟨t, ht, ht'⟩ := hS _ hcomp
  refine ⟨t, ?_, ?_⟩
  · intro V b hb
    refine (ht ((Functor.prodSectionSnd d).map b) hb).trans ?_
    change Q.map (𝟙 ((d, V) : D × C)).op (y b hb) = y b hb
    exact Q.map_id_apply _ _
  · intro t' ht2
    exact ht' t' fun Y g hg => Functor.map_op_apply_comp Q (hfac g) (ht2 g.2 hg)

/-- **The sheaf condition on `D × C` is the levelwise sheaf condition.** A presheaf on `D × C`
which is a sheaf for the topology inherited from `(C, J)` along the second projection restricts
to a `J`-sheaf on every slice `{d} × C`.

This is the converse of `CategoryTheory.Presheaf.isSheaf_inheritedTopology_prodSnd`: the preimage
of a covering sieve is a covering sieve of the inherited topology
(`CategoryTheory.Prod.functorPullback_snd_mem_inheritedTopology`), and being a sheaf for it is
being a sheaf for the original sieve on the slice
(`CategoryTheory.Presieve.isSheafFor_prodSectionSnd_of_isSheafFor_functorPullback_snd`). As in
`isSheaf_inheritedTopology_prodSnd`, coefficients in an arbitrary category reduce to
`Type`-valued coefficients by the definition of a sheaf with values in a category. -/
theorem Presheaf.isSheaf_prodSectionSnd_of_isSheaf_inheritedTopology (J : GrothendieckTopology C)
    (P : (D × C)ᵒᵖ ⥤ A) (h : Presheaf.IsSheaf ((Prod.snd D C).inheritedTopology J) P) (d : D) :
    Presheaf.IsSheaf J ((Functor.prodSectionSnd d).op ⋙ P) := by
  intro E U S hS
  exact Presieve.isSheafFor_prodSectionSnd_of_isSheafFor_functorPullback_snd _ d S
    (h E _ (Prod.functorPullback_snd_mem_inheritedTopology J d hS))

end ProductSite

end CategoryTheory

namespace Stacks.SimplicialModules

section Equivalence

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- The presheaf on `Δ × C` obtained by uncurrying a simplicial sheaf on `C`. This is
`Stacks.SimplicialModules.associatedRingPresheaf` with its coefficients left free. -/
abbrev associatedPresheaf {A : Type u₁} [Category.{v₁} A]
    (G : CategoryTheory.SimplicialObject (Sheaf J A)) : (SimplexCategory × C)ᵒᵖ ⥤ A :=
  (prodOpEquiv SimplexCategory (D := C)).functor ⋙
    Functor.uncurry.obj (G ⋙ sheafToPresheaf J A)

/-- The restriction of the uncurrying of `G` along `(φ, ψ)` is the structure map of `G` at `φ`
followed by the restriction of `G m` along `ψ`. This is the definition of uncurrying, and it is
what every naturality check below is read off. -/
lemma associatedPresheaf_map {A : Type u₁} [Category.{v₁} A]
    (G : CategoryTheory.SimplicialObject (Sheaf J A)) {m n : SimplexCategory} (φ : m ⟶ n)
    {U V : C} (ψ : U ⟶ V) :
    (associatedPresheaf J G).map (φ ×ₘ ψ).op
      = (G.map φ.op).hom.app (op V) ≫ (G.obj (op m)).obj.map ψ.op := rfl

/-- The uncurrying of a simplicial sheaf is a sheaf for the topology `Δ × C` inherits from
`(C, J)` along the second projection: being a sheaf there is the levelwise condition
(`CategoryTheory.Presheaf.isSheaf_inheritedTopology_prodSnd`), and in the level `n` the uncurried
presheaf is the underlying presheaf of the sheaf `G n`. This is
`Stacks.SimplicialModules.isSheaf_associatedRingPresheaf` with its coefficients left free. -/
theorem isSheaf_associatedPresheaf {A : Type u₁} [Category.{v₁} A]
    (G : CategoryTheory.SimplicialObject (Sheaf J A)) :
    Presheaf.IsSheaf ((CategoryTheory.Prod.snd SimplexCategory C).inheritedTopology J)
      (associatedPresheaf J G) := by
  refine Presheaf.isSheaf_inheritedTopology_prodSnd J _ fun n => ?_
  refine (Presheaf.isSheaf_of_iso_iff
    (NatIso.ofComponents (fun _ => Iso.refl _) (by intros; simp [Functor.prodSectionSnd]) :
      (Functor.prodSectionSnd n).op ⋙ associatedPresheaf J G ≅ (G.obj (op n)).obj)).2
    (G.obj (op n)).property

/-- **Stacks 09D0.** A sheaf on `Δ × C` read as a simplicial sheaf on `C`: the level `n` is the
restriction of `F` to the fibre `{n} × C`, which is a sheaf by
`CategoryTheory.Presheaf.isSheaf_prodSectionSnd_of_isSheaf_inheritedTopology`, and the structure
map of `φ : m ⟶ n` is the restriction of `F` along `(φ, 𝟙)`. -/
def fibrewise (A : Type u₁) [Category.{v₁} A] :
    Sheaf ((CategoryTheory.Prod.snd SimplexCategory C).inheritedTopology J) A ⥤
      CategoryTheory.SimplicialObject (Sheaf J A) where
  obj F :=
    { obj := fun n => ⟨(Functor.prodSectionSnd n.unop).op ⋙ F.obj,
        Presheaf.isSheaf_prodSectionSnd_of_isSheaf_inheritedTopology J F.obj F.property n.unop⟩
      map := fun φ => ObjectProperty.homMk
        { app := fun U => F.obj.map (φ.unop ×ₘ 𝟙 U.unop).op
          naturality := fun _ _ ψ =>
            (Functor.map_op_prod_snd_comp_fst F.obj φ.unop ψ.unop).symm.trans
              (Functor.map_op_prod_fst_comp_snd F.obj φ.unop ψ.unop) }
      map_id := fun _ => Sheaf.hom_ext (NatTrans.ext (funext fun _ => F.obj.map_id _))
      map_comp := fun φ ψ => Sheaf.hom_ext (NatTrans.ext (funext fun U =>
        Functor.map_op_prod_comp_fst F.obj ψ.unop φ.unop U.unop)) }
  map α :=
    { app := fun n => ObjectProperty.homMk
        (Functor.whiskerLeft (Functor.prodSectionSnd n.unop).op α.hom)
      naturality := fun _ _ _ => Sheaf.hom_ext (NatTrans.ext (funext fun _ =>
        α.hom.naturality _)) }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **Stacks 09D0.** A simplicial sheaf on `C` read as a sheaf on `Δ × C`, by uncurrying. This is
the inverse of `Stacks.SimplicialModules.fibrewise`. -/
def sheafUncurry (A : Type u₁) [Category.{v₁} A] :
    CategoryTheory.SimplicialObject (Sheaf J A) ⥤
      Sheaf ((CategoryTheory.Prod.snd SimplexCategory C).inheritedTopology J) A :=
  ObjectProperty.lift _
    ((Functor.whiskeringRight _ _ _).obj (sheafToPresheaf J A) ⋙ Functor.uncurry ⋙
      (Functor.whiskeringLeft _ _ _).obj (prodOpEquiv SimplexCategory (D := C)).functor)
    (fun G => isSheaf_associatedPresheaf J G)

/-- Uncurrying the fibres of a sheaf on `Δ × C` gives it back: both round trips are the identity
on underlying presheaves, and the only thing to check is that the identity is natural, which is
the factorisation `CategoryTheory.Functor.map_op_prod_fst_comp_snd`. -/
def sheafUncurryFibrewiseIso (A : Type u₁) [Category.{v₁} A] :
    𝟭 (Sheaf ((CategoryTheory.Prod.snd SimplexCategory C).inheritedTopology J) A) ≅
      fibrewise J A ⋙ sheafUncurry J A :=
  NatIso.ofComponents
    (fun F => ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ => Iso.refl _) (by
      intro X Y f
      change F.obj.map f ≫ 𝟙 _
        = 𝟙 _ ≫ (associatedPresheaf J ((fibrewise J A).obj F)).map f
      rw [Category.comp_id, Category.id_comp]
      exact Functor.map_op_prod_fst_comp_snd F.obj f.unop.1 f.unop.2)))
    (by
      intro F F' α
      refine Sheaf.hom_ext (NatTrans.ext (funext fun X => ?_))
      change α.hom.app X ≫ 𝟙 _ = 𝟙 _ ≫ α.hom.app X
      rw [Category.comp_id, Category.id_comp])

/-- The fibres of the uncurrying of a simplicial sheaf are the sheaves one started with. -/
def fibrewiseSheafUncurryIso (A : Type u₁) [Category.{v₁} A] :
    sheafUncurry J A ⋙ fibrewise J A ≅ 𝟭 (CategoryTheory.SimplicialObject (Sheaf J A)) :=
  NatIso.ofComponents
    (fun G => NatIso.ofComponents
      (fun n => ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ => Iso.refl _) (by
        intro U V ψ
        change (associatedPresheaf J G).map (𝟙 n.unop ×ₘ ψ.unop).op ≫ 𝟙 _
          = 𝟙 _ ≫ (G.obj n).obj.map ψ
        rw [associatedPresheaf_map]
        simp)))
      (by
        intro m n φ
        refine Sheaf.hom_ext (NatTrans.ext (funext fun U => ?_))
        change (associatedPresheaf J G).map (φ.unop ×ₘ 𝟙 U.unop).op ≫ 𝟙 _
          = 𝟙 _ ≫ (G.map φ).hom.app U
        rw [associatedPresheaf_map]
        simp))
    (by
      intro G G' α
      refine NatTrans.ext (funext fun n => Sheaf.hom_ext (NatTrans.ext (funext fun U => ?_)))
      change (α.app n).hom.app U ≫ 𝟙 _ = 𝟙 _ ≫ (α.app n).hom.app U
      rw [Category.comp_id, Category.id_comp])

/-- **Stacks 09D0.** A sheaf on `Δ × C` *is* a simplicial sheaf on `C`: levelwise restriction to
the fibres and uncurrying are an equivalence of categories. -/
@[stacks 09D0 "a simplicial sheaf on C is the same thing as a sheaf on Δ × C for the topology \
  inherited along π"]
def simplicialSheafEquivalence (A : Type u₁) [Category.{v₁} A] :
    Sheaf ((CategoryTheory.Prod.snd SimplexCategory C).inheritedTopology J) A ≌
      CategoryTheory.SimplicialObject (Sheaf J A) :=
  CategoryTheory.Equivalence.mk (fibrewise J A) (sheafUncurry J A)
    (sheafUncurryFibrewiseIso J A) (fibrewiseSheafUncurryIso J A)

end Equivalence

section Abelian

open Stacks.Cohomology.DerivedLowerShriek

variable (C : Type w) [SmallCategory C] (J : GrothendieckTopology C)
  [(projection C).IsContinuous (projectionTopology C J) J]
  [(projection C).IsCocontinuous (projectionTopology C J) J]
  [HasSheafify (projectionTopology C J) AddCommGrpCat.{w}]
  [HasSheafify J AddCommGrpCat.{w}]
  [((projection C).sheafPushforwardContinuous AddCommGrpCat.{w}
    (projectionTopology C J) J).IsRightAdjoint]

/-- **Stacks 09D0.** Reading the inverse image of the projection fibrewise gives the constant
simplicial sheaf: the fibre inclusion `i_n` followed by `π` is the identity, so every component
is the identity, and the structure maps of the simplicial sheaf are restrictions of `F` along
identities. -/
def fibrewiseCompInverseImageIso :
    abelianRestriction.{w} (projectionTopology C J) J (projection C) ⋙
        fibrewise J AddCommGrpCat.{w} ≅
      CategoryTheory.Functor.const SimplexCategoryᵒᵖ :=
  NatIso.ofComponents
    (fun F => NatIso.ofComponents (fun _ => Iso.refl _) (by
      intro m n φ
      refine Sheaf.hom_ext (NatTrans.ext (funext fun U => ?_))
      change F.obj.map (𝟙 (op U.unop)) ≫ 𝟙 _ = 𝟙 _ ≫ 𝟙 _
      rw [Category.comp_id, Category.id_comp, F.obj.map_id]))
    (by
      intro F F' α
      refine NatTrans.ext (funext fun n => Sheaf.hom_ext (NatTrans.ext (funext fun U => ?_)))
      change α.hom.app U ≫ 𝟙 _ = 𝟙 _ ≫ α.hom.app U
      rw [Category.comp_id, Category.id_comp])

/-- The right adjoint of `fibrewise ⋙ colim` is the inverse image of the projection: it is
`Functor.const ⋙ sheafUncurry` by the adjunctions, and that is restriction along `π` by
`Stacks.SimplicialModules.fibrewiseCompInverseImageIso` together with the equivalence. -/
def constCompSheafUncurryIso :
    CategoryTheory.Functor.const SimplexCategoryᵒᵖ ⋙ sheafUncurry J AddCommGrpCat.{w} ≅
      abelianRestriction.{w} (projectionTopology C J) J (projection C) :=
  ((Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _ (sheafUncurryFibrewiseIso J AddCommGrpCat.{w}) ≪≫
    Functor.isoWhiskerRight (fibrewiseCompInverseImageIso C J)
      (sheafUncurry J AddCommGrpCat.{w})).symm

variable [HasColimitsOfShape SimplexCategoryᵒᵖ (Sheaf J AddCommGrpCat.{w})]

/-- **Stacks 09D0.** `π_!` on abelian sheaves is the colimit over `Δᵒᵖ` of the simplicial sheaf
that a sheaf on `Δ × C` is.

Both sides are left adjoints of restriction along `π`: the left-hand side by
`Stacks.Cohomology.DerivedLowerShriek.abelianAdjunction`, and the right-hand side because
`fibrewise` is an equivalence, `colim` is left adjoint to the constant simplicial sheaf, and the
composite right adjoint is restriction along `π` by
`Stacks.SimplicialModules.constCompSheafUncurryIso`. -/
def abelianLowerShriekIsoColim :
    abelianLowerShriek.{w} (projectionTopology C J) J (projection C) ≅
      fibrewise J AddCommGrpCat.{w} ⋙
        (colim : (SimplexCategoryᵒᵖ ⥤ Sheaf J AddCommGrpCat.{w}) ⥤
          Sheaf J AddCommGrpCat.{w}) :=
  Adjunction.leftAdjointUniq
    (abelianAdjunction.{w} (projectionTopology C J) J (projection C))
    (((simplicialSheafEquivalence J AddCommGrpCat.{w}).toAdjunction.comp
      colimConstAdj).ofNatIsoRight (constCompSheafUncurryIso C J))

end Abelian

end Stacks.SimplicialModules

end
