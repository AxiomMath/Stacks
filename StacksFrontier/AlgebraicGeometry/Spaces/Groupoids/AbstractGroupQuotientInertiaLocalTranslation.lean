module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.AbstractGroupQuotientStackInertia

/-!
# The automorphism of an inertia point is locally multiplication by an element of `G`

Stacks 0374 computes the inertia stack of the quotient `[[X/G]]` of a sheaf `X` by an
abstract commutative group `G`. Its argument rests on the sentence

> Since `G` is a sheaf of commutative groups, `α` is, locally in the fppf topology over
> `T`, given by multiplication by some element `g` of `G`.

for a `T`-point `(P/T, φ, α)` of `I_{[X/G]}`. This file proves that sentence.

`AlgebraicGeometry.existsUnique_auto_eq_totalSmul` already identifies `α`, at a single
section of the total space of the torsor, with multiplication by a unique *section* of the
constant sheaf of groups. A section of that sheaf is a section of a sheafification, not an
element of `G`, so by itself it does not index a summand of `∐_{g ∈ G} [X^g/G]`. What is
proved here is the passage from such a section to an element of `G`: the unit of
sheafification is locally surjective, so over a covering of the base the section comes from
an element `g ∈ G`, and there multiplication by that section *is* multiplication by `g`.

## Main definitions

* `AlgebraicGeometry.autoTranslationSieve`: the sieve of arrows `f : V ⟶ U` over the base
  `U` of an object of `I_{[X/G]}` along which its automorphism is multiplication by a single
  element of `G`, at every section of the total space of the torsor lying over `f`.

## Main results

* `CategoryTheory.isLocallySurjective_toSheafify_grpCat`: every section of the
  sheafification of a presheaf of groups is, on a covering, the image of a section of the
  presheaf. This is the multiplicative counterpart of
  `CategoryTheory.isLocallySurjective_toSheafify_addCommGrp`, and like it is proved for a
  group universe unrelated to the universes of the site: the sections locally in the image
  form a subpresheaf of groups, that subpresheaf is a sheaf, and the universal property of
  sheafification splits its inclusion.
* `AlgebraicGeometry.autoTranslationSieve_mem`: that sieve is a covering sieve.
* `AlgebraicGeometry.exists_covering_auto_eq_translation`: **Stacks 0374**, the sentence
  quoted above.

## Implementation notes

Two inputs make the local statement propagate from one section of the torsor to all of
them. Commutativity of `G` enters through
`CategoryTheory.constantSheafOfGroupsUnit_central`: two sections of the total space over the
same morphism differ by a section `ε` of the constant sheaf of groups, `α` is equivariant
for `ε`, and multiplication by `ε` commutes with multiplication by the section attached to
`g` only because the latter is central. Compatibility with restriction enters through
`CategoryTheory.constantSheafOfGroupsUnit_naturality`: the section attached to `g` restricts
to the section attached to `g`, so the element of `G` found over a member of the covering
serves over everything above it, which is what makes the collection of such arrows a sieve.

Mathlib's `CategoryTheory.Presheaf.isLocallySurjective_toSheafify'` is not usable here. It
requires the carrier universe of the target category to be the universe `max u v` fixed by
the site, whereas the group `G` of Stacks 0374 has a universe of its own, unrelated to the
universes of the big fppf site.

## References

* [Stacks Project, Tag 0374](https://stacks.math.columbia.edu/tag/0374)
* [Stacks Project, Tag 0371](https://stacks.math.columbia.edu/tag/0371)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

universe w v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- The sections of `H` lying locally in the image of a morphism `η : P ⟶ H` of presheaves
of groups, as a subgroup of the sections of `H`. -/
private def localImageSubgroupGrp {P H : Cᵒᵖ ⥤ GrpCat.{w}} (η : P ⟶ H) (V : Cᵒᵖ) :
    Subgroup (H.obj V) where
  carrier := ((Subfunctor.range (Functor.whiskerRight η (forget GrpCat))).sheafify J).obj V
  one_mem' := Subfunctor.le_sheafify _ _ _ ⟨1, (η.app V).hom.map_one⟩
  mul_mem' := by
    intro x y hx hy
    apply J.superset_covering _ (J.intersection_covering hx hy)
    intro W f hf
    obtain ⟨a, ha⟩ := hf.1
    obtain ⟨b, hb⟩ := hf.2
    refine ⟨a * b, ?_⟩
    change (η.app (op W)).hom (a * b) = (H.map f.op).hom (x * y)
    simp only [map_mul]
    exact congrArg₂ (· * ·) ha hb
  inv_mem' := by
    intro x hx
    apply J.superset_covering _ hx
    intro W f hf
    obtain ⟨a, ha⟩ := hf
    refine ⟨a⁻¹, ?_⟩
    change (η.app (op W)).hom a⁻¹ = (H.map f.op).hom x⁻¹
    simp only [map_inv]
    exact congrArg Inv.inv ha

/-- The subpresheaf of groups of sections lying locally in the image of `η`. -/
private def localImageGrp {P H : Cᵒᵖ ⥤ GrpCat.{w}} (η : P ⟶ H) : Cᵒᵖ ⥤ GrpCat.{w} where
  obj V := GrpCat.of (localImageSubgroupGrp J η V)
  map f := GrpCat.ofHom
    { toFun := fun x => ⟨(H.map f).hom x,
        ((Subfunctor.range (Functor.whiskerRight η (forget GrpCat))).sheafify J).map f x.property⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun x y => Subtype.ext ((H.map f).hom.map_mul x.val y.val) }

/-- The inclusion into `H` of the sections lying locally in the image of `η`. -/
private def localImageGrpι {P H : Cᵒᵖ ⥤ GrpCat.{w}} (η : P ⟶ H) : localImageGrp J η ⟶ H where
  app V := GrpCat.ofHom (localImageSubgroupGrp J η V).subtype

/-- The factorization of `η` through the sections lying locally in its image. -/
private def toLocalImageGrp {P H : Cᵒᵖ ⥤ GrpCat.{w}} (η : P ⟶ H) : P ⟶ localImageGrp J η where
  app V := GrpCat.ofHom
    { toFun := fun x => ⟨(η.app V).hom x, Subfunctor.le_sheafify _ _ _ ⟨x, rfl⟩⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun x y => Subtype.ext (map_mul _ x y) }
  naturality V W f := by
    ext x
    exact Subtype.ext (η.naturality_apply f x)

private lemma isSheaf_localImageGrp {P H : Cᵒᵖ ⥤ GrpCat.{w}} (η : P ⟶ H)
    (hH : Presheaf.IsSheaf J H) : Presheaf.IsSheaf J (localImageGrp J η) := by
  apply Presheaf.isSheaf_of_isSheaf_comp J (localImageGrp J η) (forget GrpCat)
  show Presheaf.IsSheaf J
    ((Subfunctor.range (Functor.whiskerRight η (forget GrpCat))).sheafify J).toFunctor
  exact (isSheaf_iff_isSheaf_of_type _ _).mpr
    ((Subfunctor.range (Functor.whiskerRight η (forget GrpCat))).sheafify_isSheaf
      ((isSheaf_iff_isSheaf_of_type _ _).mp
        (Presheaf.isSheaf_comp_of_isSheaf J H (forget GrpCat) hH)))

/-- Sheafification of a presheaf of groups is locally surjective: every section of the
sheafification is, on a covering, the image of a section of the presheaf. The universe of
the groups is unrelated to the universes of the site, which is what the constant sheaf of
groups on a big site needs. -/
instance isLocallySurjective_toSheafify_grpCat [HasWeakSheafify J GrpCat.{w}]
    (P : Cᵒᵖ ⥤ GrpCat.{w}) : Presheaf.IsLocallySurjective J (toSheafify J P) := by
  let H := sheafify J P
  let η := toSheafify J P
  have hH : Presheaf.IsSheaf J H := ((presheafToSheaf J GrpCat).obj P).property
  let l : H ⟶ localImageGrp J η :=
    sheafifyLift J (toLocalImageGrp J η) (isSheaf_localImageGrp J η hH)
  have hl : l ≫ localImageGrpι J η = 𝟙 H := by
    apply sheafify_hom_ext J _ _ hH
    rw [← Category.assoc, toSheafify_sheafifyLift]
    ext V x
    rfl
  rw [Presheaf.isLocallySurjective_iff_range_sheafify_eq_top]
  apply top_unique
  intro V x _
  have he := congrArg (fun k : H ⟶ H => (k.app V).hom x) hl
  change (((l.app V).hom x).val) = x at he
  change x ∈ ((Subfunctor.range (Functor.whiskerRight η (forget GrpCat))).sheafify J).obj V
  rw [← he]
  exact ((l.app V).hom x).property

end CategoryTheory

namespace AlgebraicGeometry

universe t z w u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {G : Type w} [CommGroup G]
  [HasWeakSheafify (BigFppfOver.topology B S hS) GrpCat.{w}]
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type z} {ρ : G →* Aut X}

open AbstractGroupQuotientStack

/-- If the automorphism of an object of `I_{[X/G]}` is multiplication by `g ∈ G` at one
section of the total space of its torsor, then it is multiplication by `g` at every section
lying over the same morphism. Two such sections differ by a section of the constant sheaf of
groups, the automorphism is equivariant for it, and it commutes with the section attached to
`g` because `G` is commutative. -/
lemma auto_eq_translationMap_of_eq_at_section (Z : quotientInertia B S hS G X ρ)
    {V : (BigFppfOver B S hS)ᵒᵖ} (g : G) {p q : Z.obj.Total V}
    (hp : Z.auto.asIso.hom.map V p = Z.obj.translationMap g V p) (hq : q.1 = p.1) :
    Z.auto.asIso.hom.map V q = Z.obj.translationMap g V q := by
  obtain ⟨ε, rfl, -⟩ := Z.obj.existsUnique_totalSmul_eq p q hq
  rw [Z.auto.asIso.hom.map_equivariant V ε p, hp, translationMap, translationMap,
    ← Z.obj.totalSmul_mul, ← Z.obj.totalSmul_mul, constantSheafOfGroupsUnit_central]

/-- If the automorphism of an object of `I_{[X/G]}` is multiplication by the section `δ` of
the constant sheaf of groups at a section `p` of the total space of its torsor over `V`, and
`δ` restricts along `k : W ⟶ V` to the section attached to `g ∈ G`, then over everything
above `W` the automorphism is multiplication by `g`. -/
lemma auto_eq_translationMap_of_restrict (Z : quotientInertia B S hS G X ρ)
    {V W W' : BigFppfOver B S hS} (p : Z.obj.Total (op V))
    (δ : (constantSheafOfGroups (BigFppfOver.topology B S hS) G).presheaf.obj (op V))
    (hp : Z.auto.asIso.hom.map (op V) p = Z.obj.totalSmul δ p) (k : W ⟶ V) (g : G)
    (hg : (constantSheafOfGroups (BigFppfOver.topology B S hS) G).presheaf.map k.op δ =
      constantSheafOfGroupsUnit (BigFppfOver.topology B S hS) G (op W) g)
    (m : W' ⟶ W) (q : Z.obj.Total (op W')) (hq : q.1 = (m ≫ k) ≫ p.1) :
    Z.auto.asIso.hom.map (op W') q = Z.obj.translationMap g (op W') q := by
  have hq₀ : Z.auto.asIso.hom.map (op W') (Z.obj.totalMap (m ≫ k).op p) =
      Z.obj.translationMap g (op W') (Z.obj.totalMap (m ≫ k).op p) := by
    rw [Z.auto.asIso.hom.map_naturality (m ≫ k).op p, hp, Z.obj.totalMap_totalSmul,
      show (constantSheafOfGroups (BigFppfOver.topology B S hS) G).presheaf.map (m ≫ k).op δ =
        constantSheafOfGroupsUnit (BigFppfOver.topology B S hS) G (op W') g by
        rw [op_comp, Functor.map_comp_apply, hg, constantSheafOfGroupsUnit_naturality]]
    rfl
  exact auto_eq_translationMap_of_eq_at_section Z g hq₀ hq

/-- The sieve of arrows `f : V ⟶ U` over the base `U` of an object of `I_{[X/G]}` along
which its automorphism is multiplication by a single element of `G`: at every section of the
total space of the torsor lying over `f`, and over every object above `V`. -/
def autoTranslationSieve (Z : quotientInertia B S hS G X ρ) : Sieve Z.obj.base where
  arrows V f := ∃ g : G, ∀ (W : BigFppfOver B S hS) (k : W ⟶ V) (q : Z.obj.Total (op W)),
    q.1 = k ≫ f → Z.auto.asIso.hom.map (op W) q = Z.obj.translationMap g (op W) q
  downward_closed := by
    rintro V W f ⟨g, hg⟩ k
    exact ⟨g, fun W' l q hq => hg W' (l ≫ k) q (hq.trans (Category.assoc _ _ _).symm)⟩

/-- The arrows along which the automorphism of an object of `I_{[X/G]}` is multiplication by
a single element of `G` cover its base. The torsor has sections locally, at a section the
automorphism is multiplication by a section of the constant sheaf of groups, and that
section is locally the image of an element of `G`. -/
theorem autoTranslationSieve_mem (Z : quotientInertia B S hS G X ρ) :
    autoTranslationSieve Z ∈ (BigFppfOver.topology B S hS) Z.obj.base := by
  obtain ⟨R, hR, hsec⟩ := Z.obj.isTorsor (Over.mk (𝟙 Z.obj.base))
  refine (BigFppfOver.topology B S hS).transitive
    (((BigFppfOver.topology B S hS).mem_over_iff R).mp hR) _ fun V f hf => ?_
  have hk : R (Over.homMk f (by simp) : (Over.mk f : Over Z.obj.base) ⟶
      Over.mk (𝟙 Z.obj.base)) := by
    rw [← (Sieve.overEquiv (Over.mk (𝟙 Z.obj.base))).symm_apply_apply R]
    exact hf
  obtain ⟨s⟩ := hsec hk
  obtain ⟨δ, hδ, -⟩ := existsUnique_auto_eq_totalSmul Z (op V) ⟨f, s⟩
  refine (BigFppfOver.topology B S hS).superset_covering ?_
    (Presheaf.imageSieve_mem (BigFppfOver.topology B S hS)
      (toSheafify (BigFppfOver.topology B S hS)
        ((Functor.const (BigFppfOver B S hS)ᵒᵖ).obj (GrpCat.of G))) δ)
  rintro W l ⟨g, hg⟩
  exact ⟨g, fun W' m q hq => auto_eq_translationMap_of_restrict Z ⟨f, s⟩ δ hδ.symm l g hg.symm
    m q (hq.trans (Category.assoc _ _ _).symm)⟩

/-- **Stacks 0374.** The source's sentence "Since `G` is a sheaf of commutative groups, `α`
is, locally in the fppf topology over `T`, given by multiplication by some element `g` of
`G`": for an object `(P/T, φ, α)` of the inertia stack `I_{[X/G]}` of the quotient
`[[X/G]]` there is an fppf covering of `T` over each member of which a single element `g` of
`G` has `α` equal to multiplication by `g`, at every section of the total space of `P` lying
over that member. -/
theorem exists_covering_auto_eq_translation (Z : quotientInertia B S hS G X ρ) :
    ∃ R ∈ (BigFppfOver.topology B S hS) Z.obj.base,
      ∀ ⦃V : BigFppfOver B S hS⦄ (f : V ⟶ Z.obj.base), R f →
        ∃ g : G, ∀ (W : BigFppfOver B S hS) (k : W ⟶ V) (q : Z.obj.Total (op W)),
          q.1 = k ≫ f → Z.auto.asIso.hom.map (op W) q = Z.obj.translationMap g (op W) q :=
  ⟨autoTranslationSieve Z, autoTranslationSieve_mem Z, fun _ _ hf => hf⟩

end AlgebraicGeometry

end
