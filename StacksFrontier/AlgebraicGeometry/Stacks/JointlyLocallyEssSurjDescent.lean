module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Properties.MorphismFinitenessFamily
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationDescentComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatDescentAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.MorphismSpaceIsoClass
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasBridges
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveFlatFppfLocalSections

/-!
# Descent of flatness along a jointly locally essentially surjective family (Stacks 06NR)

**Stacks 06NR** says that for morphisms of algebraic spaces `X ⟶ Y ⟶ Z`, if `X ⟶ Z` is flat
(resp. locally of finite presentation) and `X ⟶ Y` is a surjection of fppf sheaves, then
`Y ⟶ Z` is flat (resp. locally of finite presentation). This file proves the analogue for
1-morphisms of algebraic stacks, with the single first factor replaced by a family: if
`a j : 𝒜 j ⟶ ℬ` is *jointly locally essentially surjective* — every object of a fibre of `ℬ` is,
over the members of a covering sieve, isomorphic to the image of an object of some `𝒜 j` — and
every composite `a j ≫ c` with `c : ℬ ⟶ 𝒞` is flat (resp. locally of finite presentation), then
`c` is.

No hypothesis of flatness is made on the `a j`, which is what distinguishes this from
**Stacks 06Q0** and **Stacks 06Q9**; that is what lets it make the flatness of a gerbe out of
nothing but the flatness of a smooth presentation, see
`StacksFrontier.AlgebraicGeometry.Stacks.GerbeFlatness`. A family rather than a single 1-morphism is
needed because the local objects a gerbe supplies live over the members of an fppf covering,
whose disjoint union need not be an object of the big fppf site.

## Main definitions

* `AlgebraicGeometry.Stack.IsJointlyLocallyEssSurj`: joint local essential surjectivity of a
  family of 1-morphisms of categories fibred in groupoids over the big fppf site of `S`.

## Main results

* `AlgebraicGeometry.Stack.IsJointlyLocallyEssSurj.comp` and
  `AlgebraicGeometry.Stack.IsJointlyLocallyEssSurj.fst_of_isTwoFibreProduct`: the condition is
  stable under composition and base change.
* `AlgebraicGeometry.Stack.iSup_imageSieve_representingMap_mem`: between represented stacks, it
  makes the induced morphisms of representing presheaves jointly surjective as morphisms of
  sheaves.
* `AlgebraicGeometry.Stack.isJointlyLocallyEssSurj_schemeFibredCategoryMap`: the members of an
  fppf covering family are jointly locally essentially surjective onto the represented stack.
* `AlgebraicGeometry.Stack.isFlat_of_chart_family` and
  `AlgebraicGeometry.Stack.isLocallyOfFinitePresentation_of_chart_family`: the two properties
  pass to a morphism of algebraic spaces from a jointly locally essentially surjective family of
  charts over it.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_of_isJointlyLocallyEssSurj_of_isFlat_comp` and
  its sibling `isLocallyOfFinitePresentation_of_isJointlyLocallyEssSurj_of_comp`: **Stacks 06NR**
  for 1-morphisms of algebraic stacks along a jointly locally essentially surjective family.

## Implementation notes

The proof of the stack statement is that of Stacks 06Q0
(`AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_of_comp_of_isSurjective_of_isFlat`), run once for
every member of the family; the space-level step it ends with is
`AlgebraicGeometry.Space.isFlat_of_comp_of_jointlyLocallySurjective`, Stacks 06NR for a jointly
surjective family of morphisms of algebraic spaces, in place of the descent of flatness along a
surjective flat morphism.

## References

* [Stacks Project, Tag 045D](https://stacks.math.columbia.edu/tag/045D)
* [Stacks Project, Tag 06NR](https://stacks.math.columbia.edu/tag/06NR)
* [Stacks Project, Tag 06Q0](https://stacks.math.columbia.edu/tag/06Q0)
* [Stacks Project, Tag 06Q9](https://stacks.math.columbia.edu/tag/06Q9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Bicategory

namespace AlgebraicGeometry.Stack

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Joint local essential surjectivity -/

/-- A family of 1-morphisms `a j : 𝒜 j ⟶ ℬ` of categories fibred in groupoids over the big fppf
site of `S` is *jointly locally essentially surjective* when every object `y` of a fibre of `ℬ`
over `U` becomes, over every arrow `k` of some covering sieve of `U`, isomorphic to the image of an
object of some `𝒜 j`; the isomorphism is rendered as a morphism to `y` lying over `k`, which in a
category fibred in groupoids is an isomorphism with the restriction of `y`.

For a one-member family this is the local essential surjectivity that Stacks 045D consumes. -/
abbrev IsJointlyLocallyEssSurj {J : Type v}
    {𝒜 : J → CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {ℬ : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (a : ∀ j, 𝒜 j ⟶ ℬ) : Prop :=
  ∀ (U : BigFppfOver B S hS) (y : ℬ.val.p.Fiber U),
    ∃ R ∈ BigFppfOver.topology B S hS U,
      ∀ ⦃V : BigFppfOver B S hS⦄ ⦃k : V ⟶ U⦄, R.arrows k →
        ∃ (j : J) (z : (𝒜 j).val.obj)
          (φ : (CatFiberedInGroupoids.homFunctor (a j)).obj z ⟶ y.1), ℬ.val.p.IsHomLift k φ

variable {B S hS}

/-- The source of an object over `a z` lifting a morphism `k` lies over the source of `k`. -/
private theorem obj_p_eq_of_homFunctor_isHomLift
    {𝒜 ℬ : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} (a : 𝒜 ⟶ ℬ)
    {z : 𝒜.val.obj} {y : ℬ.val.obj} {V U : BigFppfOver B S hS} {k : V ⟶ U}
    {φ : (CatFiberedInGroupoids.homFunctor a).obj z ⟶ y} (hφ : ℬ.val.p.IsHomLift k φ) :
    𝒜.val.p.obj z = V :=
  (Functor.congr_obj (CatFiberedInGroupoids.homFunctor_comp_p a) z).symm.trans
    (IsHomLift.domain_eq ℬ.val.p k φ)

/-- A single locally essentially surjective 1-morphism is a jointly locally essentially
surjective one-member family. -/
theorem IsJointlyLocallyEssSurj.of_localEssSurj
    {𝒜 ℬ : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} (a : 𝒜 ⟶ ℬ)
    (ha : ∀ (U : BigFppfOver B S hS) (y : ℬ.val.p.Fiber U),
      ∃ R ∈ BigFppfOver.topology B S hS U,
        ∀ ⦃V : BigFppfOver B S hS⦄ ⦃k : V ⟶ U⦄, R.arrows k →
          ∃ z : 𝒜.val.obj, ∃ φ : (CatFiberedInGroupoids.homFunctor a).obj z ⟶ y.1,
            ℬ.val.p.IsHomLift k φ) :
    IsJointlyLocallyEssSurj B S hS (fun _ : PUnit.{v + 1} => a) := by
  intro U y
  obtain ⟨R, hR, hRl⟩ := ha U y
  refine ⟨R, hR, fun V k hk => ?_⟩
  obtain ⟨z, φ, hφ⟩ := hRl hk
  exact ⟨PUnit.unit, z, φ, hφ⟩

/-- **Joint local essential surjectivity is stable under composition.** If `a j : 𝒜 j ⟶ ℬ` is
jointly locally essentially surjective and, for every `j`, so is a family
`b j i : 𝒞 j i ⟶ 𝒜 j`, then the family of composites `b j i ≫ a j`, indexed by the pairs `(j, i)`,
is jointly locally essentially surjective.

The covering sieve is the bind of the sieve for the `a j` with, over each of its arrows, the sieve
for the `b j` at the chosen lift. -/
theorem IsJointlyLocallyEssSurj.comp {J : Type v}
    {𝒜 : J → CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {ℬ : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {a : ∀ j, 𝒜 j ⟶ ℬ} (ha : IsJointlyLocallyEssSurj B S hS a)
    {I : J → Type v} {𝒞 : ∀ j, I j → CatFiberedInGroupoids.{u, u, u + 1, u + 1}
      (BigFppfOver B S hS)}
    {b : ∀ j i, 𝒞 j i ⟶ 𝒜 j} (hb : ∀ j, IsJointlyLocallyEssSurj B S hS (b j)) :
    IsJointlyLocallyEssSurj B S hS (fun ji : Σ j, I j => b ji.1 ji.2 ≫ a ji.1) := by
  classical
  intro U y
  obtain ⟨R, hR, hRl⟩ := ha U y
  choose j z φ hφ using hRl
  have hz : ∀ ⦃V : BigFppfOver B S hS⦄ ⦃k : V ⟶ U⦄ (hk : R.arrows k),
      (𝒜 (j hk)).val.p.obj (z hk) = V := fun V k hk =>
    obj_p_eq_of_homFunctor_isHomLift (a (j hk)) (hφ hk)
  let Rk : ∀ ⦃V : BigFppfOver B S hS⦄ ⦃k : V ⟶ U⦄, R.arrows k → Sieve V :=
    fun V k hk => (hb (j hk) V ⟨z hk, hz hk⟩).choose
  refine ⟨Sieve.bind R.arrows Rk,
    (BigFppfOver.topology B S hS).bind_covering hR
      (fun V k hk => (hb (j hk) V ⟨z hk, hz hk⟩).choose_spec.1), ?_⟩
  rintro W m ⟨V, l, k, hk, hl, rfl⟩
  obtain ⟨i, x, ψ, hψ⟩ := (hb (j hk) V ⟨z hk, hz hk⟩).choose_spec.2 hl
  refine ⟨⟨j hk, i⟩, x, (CatFiberedInGroupoids.homFunctor (a (j hk))).map ψ ≫ φ hk, ?_⟩
  exact @IsHomLift.comp _ _ _ _ ℬ.val.p _ _ _ _ _ _ l k _ _
    (PresheafOfCategories.isHomLift_map_of_comp
      (CatFiberedInGroupoids.homFunctor_comp_p (a (j hk))) l ψ hψ) (hφ hk)

/-- **Base change preserves joint local essential surjectivity, for the canonical square.** If
`a j : 𝒜 j ⟶ ℬ` is jointly locally essentially surjective, so is the family of first projections
of the canonical 2-fibre products of the cospans `(g, a j)` of Stacks 04T2.

Over an arrow `k : V ⟶ U` of the sieve for the `a j` at `g z`, a lift `φ : a j x ⟶ g z` is
compared with the image of a pullback `ζ : z₁ ⟶ z` of `z` along `k`: both lie over `k`, so the
strongly cartesian morphism `g ζ` factors `φ` through a vertical isomorphism `a j x ≅ g z₁`, which
makes `(z₁, x)` an object of the 2-fibre product over `V`. -/
theorem IsJointlyLocallyEssSurj.twoFibreProductSquare_fst {J : Type v}
    {𝒜 : J → CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {ℬ 𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {a : ∀ j, 𝒜 j ⟶ ℬ} (ha : IsJointlyLocallyEssSurj B S hS a) (g : 𝒵 ⟶ ℬ) :
    IsJointlyLocallyEssSurj B S hS
      (fun j =>
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g (a j)).fst) := by
  intro U y
  have hwg : CatFiberedInGroupoids.homFunctor g ⋙ ℬ.val.p = 𝒵.val.p :=
    CatFiberedInGroupoids.homFunctor_comp_p g
  have hgy : ℬ.val.p.obj ((CatFiberedInGroupoids.homFunctor g).obj y.1) = U :=
    (Functor.congr_obj hwg y.1).trans y.2
  obtain ⟨R, hR, hRl⟩ := ha U ⟨_, hgy⟩
  refine ⟨R, hR, fun V k hk => ?_⟩
  obtain ⟨j, x, φ, hφ⟩ := hRl hk
  obtain ⟨z₁, ζ, hζ⟩ := 𝒵.2.exists_lift k y.1 y.2
  have hgζ : ℬ.val.p.IsHomLift k ((CatFiberedInGroupoids.homFunctor g).map ζ) :=
    PresheafOfCategories.isHomLift_map_of_comp hwg k ζ hζ
  have := ℬ.2.isStronglyCartesian_homLift k ((CatFiberedInGroupoids.homFunctor g).map ζ)
  let θ := Functor.IsStronglyCartesian.map ℬ.val.p k
    ((CatFiberedInGroupoids.homFunctor g).map ζ) (Category.id_comp k).symm φ
  have : IsIso θ := ℬ.2.isIso_of_isHomLift_id θ (inferInstance : ℬ.val.p.IsHomLift (𝟙 V) θ)
  have hinv : ℬ.val.p.IsHomLift (𝟙 V) (inv θ) := inferInstance
  let P : TwoFibreProductOver 𝒵.val.p (𝒜 j).val.p ℬ.val.p (CatFiberedInGroupoids.homFunctor g)
      (CatFiberedInGroupoids.homFunctor (a j)) :=
    { base := V
      x := z₁
      y := x
      hx := IsHomLift.domain_eq 𝒵.val.p k ζ
      hy := obj_p_eq_of_homFunctor_isHomLift (a j) hφ
      iso := (asIso θ).symm
      vertical := hinv }
  exact ⟨j, P, ζ, hζ⟩

/-- **Base change preserves joint local essential surjectivity.** Let `a j : 𝒜 j ⟶ ℬ` be jointly
locally essentially surjective and let `D j` be a 2-fibre product square over the cospan
`(g, a j)`. Then the first projections of the `D j` are jointly locally essentially surjective.

The canonical squares have the property by
`AlgebraicGeometry.Stack.IsJointlyLocallyEssSurj.twoFibreProductSquare_fst`, and the comparison
1-morphism from a canonical square to `D j` carries a lift to a lift, its comparison 2-cell on the
first projection being vertical. -/
theorem IsJointlyLocallyEssSurj.fst_of_isTwoFibreProduct {J : Type v}
    {𝒜 : J → CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {ℬ 𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {a : ∀ j, 𝒜 j ⟶ ℬ} (ha : IsJointlyLocallyEssSurj B S hS a) (g : 𝒵 ⟶ ℬ)
    (D : ∀ j, Bicategory.TwoCommSq g (a j)) (hD : ∀ j, Bicategory.IsTwoFibreProduct (D j)) :
    IsJointlyLocallyEssSurj B S hS (fun j => (D j).fst) := by
  intro U y
  obtain ⟨R, hR, hRl⟩ := ha.twoFibreProductSquare_fst g U y
  refine ⟨R, hR, fun V k hk => ?_⟩
  obtain ⟨j, c, ψ, hψ⟩ := hRl hk
  let m := Bicategory.twoFibreProductPreHom (hD j)
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g (a j))
  exact ⟨j, (CatFiberedInGroupoids.homFunctor m.hom).obj c,
    m.isoFst.inv.hom.toNatTrans.app c ≫ ψ,
    @IsHomLift.comp_lift_id_left' _ _ _ _ 𝒵.val.p _ _ _ _ _ (m.isoFst.inv.hom.isHomLift' c)
      _ _ k ψ hψ⟩

variable (B S hS)

/-- **A jointly locally essentially surjective family of 1-morphisms of represented stacks
induces a jointly surjective family of morphisms of sheaves.** Let `𝒳 j` and `𝒵` be represented
by presheaves `F j` and `H`, and let `f j : 𝒳 j ⟶ 𝒵` be jointly locally essentially surjective.
Then every section of `H` over `U` lifts, over the arrows of a covering sieve of `U`, along one of
the morphisms `F j ⟶ H` of representing presheaves of Stacks 04SW.

A section `s` of `H` over `U` is named by an object `z` of `𝒵`; over every arrow `k` of the
covering sieve at `z` a lift `φ : f j x ⟶ z` makes the section named by `x` a preimage of the
restriction of `s` along `k`, by the value of the induced morphism on named sections and by the
naturality of naming. -/
theorem iSup_imageSieve_representingMap_mem {J : Type v}
    {𝒳 : J → CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (F : J → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eF : ∀ j, StacksRepresentableCFG.EquivalenceOver
      (𝒳 j).val.p (presheafOfCategories (F j ⋙ typeToCat)).p)
    (eH : StacksRepresentableCFG.EquivalenceOver
      𝒵.val.p (presheafOfCategories (H ⋙ typeToCat)).p)
    (f : ∀ j, 𝒳 j ⟶ 𝒵) (hf : IsJointlyLocallyEssSurj B S hS f)
    (U : BigFppfOver B S hS) (s : H.obj (Opposite.op U)) :
    (⨆ j, Presheaf.imageSieve (representingMap B S hS (𝒳 j) 𝒵 (F j) H (eF j) eH (f j)) s) ∈
      BigFppfOver.topology B S hS U := by
  obtain ⟨z, hz, hs⟩ := PresheafOfCategories.exists_sectionOfObj eH s
  obtain ⟨R, hR, hRl⟩ := hf U ⟨z, hz⟩
  refine (BigFppfOver.topology B S hS).superset_covering ?_ hR
  intro V k hk
  obtain ⟨j, x, φ, hφ⟩ := hRl hk
  refine (le_iSup (fun j => Presheaf.imageSieve
    (representingMap B S hS (𝒳 j) 𝒵 (F j) H (eF j) eH (f j)) s) j) k
      ⟨PresheafOfCategories.sectionOfObj (eF j) x (obj_p_eq_of_homFunctor_isHomLift (f j) hφ), ?_⟩
  rw [morphismSpaceEquiv_app_sectionOfObj, ← hs]
  exact PresheafOfCategories.sectionOfObj_map eH hz _ k φ hφ

/-! ### Charts along a jointly locally essentially surjective family -/

/-- Charts along a jointly locally essentially surjective family, for any stack property `PSt`
stable under composition, satisfied by smooth morphisms and read off on the representing
morphisms of spaces, and any space property `P` which descends along jointly surjective families.
-/
private theorem property_of_chart_family
    (PSt : ∀ {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}, (𝒳 ⟶ 𝒴) → Prop)
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (hsm : ∀ {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴), AlgebraicStacks.IsSmooth B S hS f →
      PSt f)
    (hcomp : ∀ {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵),
      PSt f → PSt g → PSt (f ≫ g))
    (hrep : ∀ {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
      (_ : IsAlgebraicSpace B S hS F) (_ : IsAlgebraicSpace B S hS G)
      (eF : StacksRepresentableCFG.EquivalenceOver 𝒳.val.val.p
        (presheafOfCategories (F ⋙ typeToCat)).p)
      (eG : StacksRepresentableCFG.EquivalenceOver 𝒴.val.val.p
        (presheafOfCategories (G ⋙ typeToCat)).p) (f : 𝒳 ⟶ 𝒴),
      PSt f → P (representingMap B S hS 𝒳.val 𝒴.val F G eF eG f.hom))
    (hglue : ∀ {J : Type v} {X : J → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
      {Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (_ : ∀ j, IsAlgebraicSpace B S hS (X j))
      (_ : IsAlgebraicSpace B S hS Y) (f : ∀ j, X j ⟶ Y) (g : Y ⟶ Z),
      (∀ j, P (f j ≫ g)) → (∀ (U : BigFppfOver B S hS) (s : Y.obj (Opposite.op U)),
        (⨆ j, Presheaf.imageSieve (f j) s) ∈ BigFppfOver.topology B S hS U) → P g)
    {V W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hV : IsAlgebraicSpace B S hS V) (hW : IsAlgebraicSpace B S hS W) (h : V ⟶ W)
    {J : Type v} {𝒰 : J → AlgebraicStacks.{u, w} B S hS}
    (u : ∀ j, 𝒰 j ⟶ algebraicSpaceStack.{u, w} B S hS V hV)
    (v : ∀ j, 𝒰 j ⟶ algebraicSpaceStack.{u, w} B S hS W hW)
    (hcomm : ∀ j, u j ≫ (Bicategory.InducedBicategory.mkHom (associatedMap B S hS h).1 :
        algebraicSpaceStack.{u, w} B S hS V hV ⟶ algebraicSpaceStack.{u, w} B S hS W hW) ≅ v j)
    (hu : IsJointlyLocallyEssSurj B S hS (fun j => (u j).hom)) (hv : ∀ j, PSt (v j)) :
    P h := by
  choose T c hcSmooth hcSurj using fun j => exists_smooth_surjective_schemeStack B S hS (𝒰 j)
  choose e heSmooth heSurj using fun j =>
    exists_smooth_surjective_algebraicSpaceStack_hom.{u, w} B S hS (T j)
  have hrSmooth : ∀ j, AlgebraicStacks.IsSmooth B S hS (e j ≫ c j) := fun j =>
    AlgebraicStacks.isSmooth_comp B S hS (e j) (c j) (heSmooth j) (hcSmooth j)
  have hr : ∀ j, IsJointlyLocallyEssSurj B S hS (fun _ : PUnit.{v + 1} => (e j ≫ c j).hom) :=
    fun j => IsJointlyLocallyEssSurj.of_localEssSurj _
      (exists_fppfCovering_fibre_lift B S hS (e j ≫ c j)
        (isSurjective_comp B S hS (e j) (c j) (heSurj j) (hcSurj j))
        (AlgebraicStacks.isFlat_of_isSmooth B S hS _ (hrSmooth j))
        (AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth B S hS _ (hrSmooth j)))
  let X : (Σ _ : J, PUnit.{v + 1}) → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
    fun ji => yoneda.obj (T ji.1)
  have hX : ∀ ji, IsAlgebraicSpace B S hS (X ji) := fun ji => isAlgebraicSpace_yoneda B S hS _
  let p : ∀ ji, X ji ⟶ V := fun ji => representingMap B S hS
    (algebraicSpaceStack.{u, w} B S hS (X ji) (hX ji)).val
    (algebraicSpaceStack.{u, w} B S hS V hV).val (X ji) V
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) ((e ji.1 ≫ c ji.1) ≫ u ji.1).hom
  have hp : ∀ ji, P (p ji ≫ h) := by
    intro ji
    have hmap := representingMap_comp_eq_of_twoIso B S hS
      (𝒰 := (algebraicSpaceStack.{u, w} B S hS (X ji) (hX ji)).val) (T := X ji) (V := V) (W := W)
      (StacksRepresentableCFG.EquivalenceOver.refl _) ((e ji.1 ≫ c ji.1) ≫ u ji.1).hom
      ((e ji.1 ≫ c ji.1) ≫ v ji.1).hom h
      (Bicategory.InducedBicategory.isoHom
        (α_ (e ji.1 ≫ c ji.1) (u ji.1) _ ≪≫
          Bicategory.whiskerLeftIso (e ji.1 ≫ c ji.1) (hcomm ji.1)))
    rw [hmap]
    exact hrep (𝒳 := algebraicSpaceStack.{u, w} B S hS (X ji) (hX ji))
      (𝒴 := algebraicSpaceStack.{u, w} B S hS W hW) (X ji) W (hX ji) hW
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) ((e ji.1 ≫ c ji.1) ≫ v ji.1)
      (hcomp _ _ (hsm _ (hrSmooth ji.1)) (hv ji.1))
  have hjs : IsJointlyLocallyEssSurj B S hS
      (fun ji : Σ _ : J, PUnit.{v + 1} => ((e ji.1 ≫ c ji.1) ≫ u ji.1).hom) :=
    hu.comp hr
  have hsieve := iSup_imageSieve_representingMap_mem B S hS
      (𝒳 := fun ji => (algebraicSpaceStack.{u, w} B S hS (X ji) (hX ji)).val) X V
      (fun _ => StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (fun ji => ((e ji.1 ≫ c ji.1) ≫ u ji.1).hom) hjs
  exact hglue hX hV p h hp hsieve

/-- **Flatness passes from a jointly locally essentially surjective family of charts to a morphism
of algebraic spaces they lie over.** Let `h : V ⟶ W` be a morphism of algebraic spaces over `S`,
and let `u j : 𝒰 j ⟶ V` and `v j : 𝒰 j ⟶ W` be 1-morphisms out of algebraic stacks over `S` with
`u j ≫ h ≅ v j`. If the `u j` are jointly locally essentially surjective and every `v j` is flat,
then `h` is flat.

Each `𝒰 j` is covered by an algebraic space `T j` through a smooth surjective chart, which is
locally essentially surjective by **Stacks 06QA**; the composites `T j ⟶ V` are therefore jointly
locally essentially surjective, so the morphisms of representing presheaves they induce are
jointly surjective as morphisms of sheaves, and their composites with `h` are the flat morphisms
induced by `T j ⟶ W`. **Stacks 06NR** for a jointly surjective family concludes. -/
theorem isFlat_of_chart_family
    {V W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hV : IsAlgebraicSpace B S hS V) (hW : IsAlgebraicSpace B S hS W) (h : V ⟶ W)
    {J : Type v} {𝒰 : J → AlgebraicStacks.{u, w} B S hS}
    (u : ∀ j, 𝒰 j ⟶ algebraicSpaceStack.{u, w} B S hS V hV)
    (v : ∀ j, 𝒰 j ⟶ algebraicSpaceStack.{u, w} B S hS W hW)
    (hcomm : ∀ j, u j ≫ (Bicategory.InducedBicategory.mkHom (associatedMap B S hS h).1 :
        algebraicSpaceStack.{u, w} B S hS V hV ⟶ algebraicSpaceStack.{u, w} B S hS W hW) ≅ v j)
    (hu : IsJointlyLocallyEssSurj B S hS (fun j => (u j).hom))
    (hvflat : ∀ j, AlgebraicStacks.IsFlat B S hS (v j)) :
    Space.IsFlat B S hS h :=
  property_of_chart_family B S hS (fun f => AlgebraicStacks.IsFlat B S hS f)
    (fun _ _ h => Space.IsFlat B S hS h) (AlgebraicStacks.isFlat_of_isSmooth B S hS)
    (AlgebraicStacks.isFlat_comp B S hS) (isFlat_representingMap_of_isFlat.{u, w} B S hS)
    (Space.isFlat_of_comp_of_jointlyLocallySurjective B S hS) hV hW h u v hcomm hu hvflat

/-- **Local finite presentation passes from a jointly locally essentially surjective family of
charts to a morphism of algebraic spaces they lie over.** In the situation of
`AlgebraicGeometry.Stack.isFlat_of_chart_family`, if every `v j` is locally of finite
presentation, then so is `h`. The proof is the same, with **Stacks 06NR** at local finite
presentation. -/
theorem isLocallyOfFinitePresentation_of_chart_family
    {V W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hV : IsAlgebraicSpace B S hS V) (hW : IsAlgebraicSpace B S hS W) (h : V ⟶ W)
    {J : Type v} {𝒰 : J → AlgebraicStacks.{u, w} B S hS}
    (u : ∀ j, 𝒰 j ⟶ algebraicSpaceStack.{u, w} B S hS V hV)
    (v : ∀ j, 𝒰 j ⟶ algebraicSpaceStack.{u, w} B S hS W hW)
    (hcomm : ∀ j, u j ≫ (Bicategory.InducedBicategory.mkHom (associatedMap B S hS h).1 :
        algebraicSpaceStack.{u, w} B S hS V hV ⟶ algebraicSpaceStack.{u, w} B S hS W hW) ≅ v j)
    (hu : IsJointlyLocallyEssSurj B S hS (fun j => (u j).hom))
    (hvlfp : ∀ j, AlgebraicStacks.IsLocallyOfFinitePresentation B S hS (v j)) :
    Space.IsLocallyOfFinitePresentation B S hS h :=
  property_of_chart_family B S hS (fun f => AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f)
    (fun _ _ h => Space.IsLocallyOfFinitePresentation B S hS h)
    (AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth B S hS)
    (AlgebraicStacks.isLocallyOfFinitePresentation_comp B S hS)
    (isLocallyOfFinitePresentation_representingMap_of_isLocallyOfFinitePresentation.{u, w}
      B S hS)
    (Space.isLocallyOfFinitePresentation_of_comp_of_jointlyLocallySurjective B S hS)
    hV hW h u v hcomm hu hvlfp

/-- **The members of an fppf covering family are jointly locally essentially surjective onto the
represented stack.** Let `m i : W i ⟶ U` be a flat, locally finitely presented and jointly
surjective family of morphisms of the big fppf site of `S`. Then the 1-morphisms of represented
categories `(Sch/S)/W i ⟶ (Sch/S)/U` they induce are jointly locally essentially surjective.

An object of `(Sch/S)/U` over `V` is a morphism `y : V ⟶ U`; over the pullback along `y` of the
covering sieve of the arrows factoring through a member of the family, `y` restricts to a
morphism which factors through some `m i`, which is the required lift. -/
theorem isJointlyLocallyEssSurj_schemeFibredCategoryMap
    {U : BigFppfOver B S hS} {I : Type (u + 1)} (W : I → B.Schemes) (m : ∀ i, W i ⟶ U.left)
    (hflat : ∀ i, Flat (B.inclusion.map (m i)))
    (hlfp : ∀ i, LocallyOfFinitePresentation (B.inclusion.map (m i)))
    (hsurj : ∀ x : (B.inclusion.obj U.left), ∃ i, x ∈ Set.range (B.inclusion.map (m i))) :
    IsJointlyLocallyEssSurj B S hS (fun i => schemeFibredCategoryMap B S hS
      (Over.homMk (m i) : (Over.mk (m i ≫ U.hom) : BigFppfOver B S hS) ⟶ U)) := by
  rintro V ⟨y, rfl⟩
  obtain ⟨R, hR, hfac⟩ := exists_mem_topology_of_family B S hS W m hflat hlfp hsurj
  refine ⟨R.pullback y.hom, (BigFppfOver.topology B S hS).pullback_stable y.hom hR,
    fun V' l hl => ?_⟩
  obtain ⟨i, b, hb⟩ := hfac hl
  let φ : (Over.mk (b ≫ (Over.homMk (m i) :
      (Over.mk (m i ≫ U.hom) : BigFppfOver B S hS) ⟶ U)) : Over U) ⟶ y :=
    Over.homMk l hb.symm
  exact ⟨i, Over.mk b, φ, IsHomLift.map (Over.forget U) φ⟩

namespace AlgebraicStacks

/-- The universal smooth-diagram criterion along a jointly locally essentially surjective family,
for a stack property `PSt` which is stable under composition and base change, holds for smooth
morphisms, and is detected on charts by the space property `P`. -/
private theorem hasPropertyOnEverySmoothDiagram_of_isJointlyLocallyEssSurj
    (PSt : ∀ {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS}, (𝒳 ⟶ 𝒴) → Prop)
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (hsm : ∀ {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴), IsSmooth B S hS f →
      PSt f)
    (hPcomp : ∀ {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵),
      PSt f → PSt g → PSt (f ≫ g))
    (hbc : ∀ {𝒳 𝒴 𝒴' : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴)
      (Q : Bicategory.TwoCommSq g f), Bicategory.IsTwoFibreProduct Q → PSt f → PSt Q.fst)
    (hchart : ∀ {V W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hV : IsAlgebraicSpace B S hS V)
      (hW : IsAlgebraicSpace B S hS W) (h : V ⟶ W) {J : Type v}
      {𝒰 : J → Stack.AlgebraicStacks.{u, w} B S hS}
      (u : ∀ j, 𝒰 j ⟶ Stack.algebraicSpaceStack.{u, w} B S hS V hV)
      (v : ∀ j, 𝒰 j ⟶ Stack.algebraicSpaceStack.{u, w} B S hS W hW),
      (∀ j, u j ≫ (Bicategory.InducedBicategory.mkHom (Stack.associatedMap B S hS h).1 :
        Stack.algebraicSpaceStack.{u, w} B S hS V hV ⟶
          Stack.algebraicSpaceStack.{u, w} B S hS W hW) ≅ v j) →
      IsJointlyLocallyEssSurj B S hS (fun j => (u j).hom) → (∀ j, PSt (v j)) → P h)
    {ℬ 𝒞 : Stack.AlgebraicStacks.{u, w} B S hS} (c : ℬ ⟶ 𝒞)
    {J : Type v} {𝒜 : J → Stack.AlgebraicStacks.{u, w} B S hS} (a : ∀ j, 𝒜 j ⟶ ℬ)
    (ha : IsJointlyLocallyEssSurj B S hS (fun j => (a j).hom)) (hac : ∀ j, PSt (a j ≫ c)) :
    Stack.HasPropertyOnEverySmoothDiagram B S hS P c.hom := by
  intro V W hV hW α β h η _hα _hβ hcomp
  -- `D` is `𝒲 ×_𝒞 ℬ` and `E j` is `(𝒲 ×_𝒞 ℬ) ×_ℬ 𝒜 j`, for `𝒲` the algebraic stack of `W`
  let bSt : Stack.algebraicSpaceStack.{u, w} B S hS W hW ⟶ 𝒞 :=
    Bicategory.InducedBicategory.mkHom β
  let D := Stack.twoFibreProductSquareAlgebraicStacks B S hS bSt c
  have hD : Bicategory.IsTwoFibreProduct D :=
    Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS bSt c
  let E := fun j => Stack.twoFibreProductSquareAlgebraicStacks B S hS D.snd (a j)
  have hE : ∀ j, Bicategory.IsTwoFibreProduct (E j) := fun j =>
    Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS D.snd (a j)
  -- the pasted rectangle exhibits `(E j).pt` over the cospan `(bSt, a j ≫ c)`
  have hDEfst : ∀ j, PSt (D.paste (E j)).fst := fun j =>
    hbc (a j ≫ c) bSt (D.paste (E j)) (Bicategory.isTwoFibreProduct_paste hD (hE j)) (hac j)
  -- the comparison 1-morphism of the given diagram into `𝒲 ×_𝒞 ℬ`, smooth by the diagram's own
  -- clause
  let Q := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} β c.hom
  have hQ : Bicategory.IsTwoFibreProduct Q :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} β c.hom
  let k₀ : Bicategory.TwoCommSq.PreHom (Stack.diagramCone B S hS c.hom α β h η) Q :=
    Quotient.out (hQ.from (Stack.diagramCone B S hS c.hom α β h η))
  let kSt : Stack.algebraicSpaceStack.{u, w} B S hS V hV ⟶ D.pt :=
    Bicategory.InducedBicategory.mkHom k₀.hom
  have hkSt : IsSmooth B S hS kSt :=
    Stack.hasPropertyOnSomeSmoothDiagram_of_isRelativelySmooth B S hS _ k₀.hom V hV
      (StacksRepresentableCFG.EquivalenceOver.refl _) (hcomp Q hQ k₀)
      (Space.isSmooth_id B S hS hV)
  -- `R j` is `𝒱 ×_{𝒲 ×_𝒞 ℬ} ((𝒲 ×_𝒞 ℬ) ×_ℬ 𝒜 j)`
  let R := fun j => Stack.twoFibreProductSquareAlgebraicStacks B S hS kSt (E j).fst
  have hR : ∀ j, Bicategory.IsTwoFibreProduct (R j) := fun j =>
    Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS kSt (E j).fst
  let hSt : Stack.algebraicSpaceStack.{u, w} B S hS V hV ⟶
      Stack.algebraicSpaceStack.{u, w} B S hS W hW :=
    Bicategory.InducedBicategory.mkHom (Stack.associatedMap B S hS h).1
  have hKst : hSt ≅ kSt ≫ D.fst :=
    Bicategory.InducedBicategory.isoMk (f := hSt) (g := kSt ≫ D.fst) k₀.isoFst
  -- the first projections of the `R j` are jointly locally essentially surjective
  have hjs : IsJointlyLocallyEssSurj B S hS (fun j => (R j).fst.hom) :=
    (ha.twoFibreProductSquare_fst D.snd.hom).twoFibreProductSquare_fst kSt.hom
  refine hchart hV hW h (fun j => (R j).fst) (fun j => (R j).snd ≫ (D.paste (E j)).fst)
    (fun j => ?_) hjs (fun j =>
      hPcomp (R j).snd (D.paste (E j)).fst
        (hsm (R j).snd (isSmooth_baseChange B S hS kSt (E j).fst (R j).swap
          (Bicategory.isTwoFibreProduct_swap (hR j)) hkSt)) (hDEfst j))
  exact Bicategory.whiskerLeftIso (R j).fst hKst ≪≫ (α_ (R j).fst kSt D.fst).symm ≪≫
    Bicategory.whiskerRightIso (R j).iso D.fst ≪≫ α_ (R j).snd (E j).fst D.fst

/-- **Stacks 06NR for 1-morphisms of algebraic stacks, flatness.** Let `c : ℬ ⟶ 𝒞` be a
1-morphism of algebraic stacks over `S` and let `a j : 𝒜 j ⟶ ℬ` be a jointly locally essentially
surjective family of 1-morphisms of algebraic stacks. If every composite `a j ≫ c` is flat, then
`c` is flat.

This is the argument of **Stacks 06Q0** with the surjective flat first factor replaced by a family
which is only jointly locally essentially surjective. Given a smooth diagram `(V, W, h)` over `c`,
the stacks `V ×_{𝒲 ×_𝒞 ℬ} ((𝒲 ×_𝒞 ℬ) ×_ℬ 𝒜 j)` project to `V` by base changes of the `a j`,
which are jointly locally essentially surjective again, and to `W` by flat 1-morphisms; so
`AlgebraicGeometry.Stack.isFlat_of_chart_family` makes `h` flat. -/
theorem isFlat_of_isJointlyLocallyEssSurj_of_isFlat_comp
    {ℬ 𝒞 : Stack.AlgebraicStacks.{u, w} B S hS} (c : ℬ ⟶ 𝒞)
    {J : Type v} {𝒜 : J → Stack.AlgebraicStacks.{u, w} B S hS} (a : ∀ j, 𝒜 j ⟶ ℬ)
    (ha : IsJointlyLocallyEssSurj B S hS (fun j => (a j).hom))
    (hac : ∀ j, IsFlat B S hS (a j ≫ c)) :
    IsFlat B S hS c :=
  (isFlat_iff_hasPropertyOnSomeSmoothDiagram B S hS c).2
    ((Stack.hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS
      (fun _ _ k => Space.IsFlat B S hS k)
      (Space.isSmoothLocalOnSourceAndTarget_flat B S hS)
      ℬ.property 𝒞.property c.hom).1
      (hasPropertyOnEverySmoothDiagram_of_isJointlyLocallyEssSurj B S hS
        (fun f => IsFlat B S hS f) (fun _ _ k => Space.IsFlat B S hS k)
        (isFlat_of_isSmooth B S hS) (isFlat_comp B S hS) (isFlat_baseChange B S hS)
        (Stack.isFlat_of_chart_family B S hS) c a ha hac))

/-- **Stacks 06NR for 1-morphisms of algebraic stacks, local finite presentation.** Let
`c : ℬ ⟶ 𝒞` be a 1-morphism of algebraic stacks over `S` and let `a j : 𝒜 j ⟶ ℬ` be a jointly
locally essentially surjective family of 1-morphisms of algebraic stacks. If every composite
`a j ≫ c` is locally of finite presentation, then so is `c`.

The proof is that of
`AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_of_isJointlyLocallyEssSurj_of_isFlat_comp`, run
for the universal criterion of Stacks 06Q2 part (1), with
`AlgebraicGeometry.Stack.isLocallyOfFinitePresentation_of_chart_family` at the end. -/
theorem isLocallyOfFinitePresentation_of_isJointlyLocallyEssSurj_of_comp
    {ℬ 𝒞 : Stack.AlgebraicStacks.{u, w} B S hS} (c : ℬ ⟶ 𝒞)
    {J : Type v} {𝒜 : J → Stack.AlgebraicStacks.{u, w} B S hS} (a : ∀ j, 𝒜 j ⟶ ℬ)
    (ha : IsJointlyLocallyEssSurj B S hS (fun j => (a j).hom))
    (hac : ∀ j, IsLocallyOfFinitePresentation B S hS (a j ≫ c)) :
    IsLocallyOfFinitePresentation B S hS c :=
  hasPropertyOnEverySmoothDiagram_of_isJointlyLocallyEssSurj B S hS
    (fun f => IsLocallyOfFinitePresentation B S hS f)
    (fun _ _ k => Space.IsLocallyOfFinitePresentation B S hS k)
    (isLocallyOfFinitePresentation_of_isSmooth B S hS) (isLocallyOfFinitePresentation_comp B S hS)
    (isLocallyOfFinitePresentation_baseChange B S hS)
    (Stack.isLocallyOfFinitePresentation_of_chart_family B S hS) c a ha hac

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
