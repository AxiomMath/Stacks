module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DirectImageSystemIdentity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleInverseImageSections
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.EtaleCover

/-!
# Sections of an inverse image over a limit of schemes

Let `X = lim X_i` be the limit of a cofiltered inverse system of schemes with affine transition
morphisms, let `H` be an abelian sheaf on the small étale site of a stage `X_{i₀}` and let `V₀` be
a quasi-compact object of that site, with base changes `V_j = V₀ ×_{X_{i₀}} X_j` and
`V = V₀ ×_{X_{i₀}} X`. The sections of the inverse images of `H` over these objects satisfy

`(f_{i₀}⁻¹H)(V) = colim_j (f_{j i₀}⁻¹H)(V_j)`,

which is the degree zero case of Stacks 09YQ for the system of inverse images of a single sheaf
(Stacks 09YN in the étale setting). This file proves the injectivity half: a section of `H` over
`V₀` whose image in `(f_{i₀}⁻¹H)(V)` vanishes already has vanishing image in `(f_{j i₀}⁻¹H)(V_j)`
for some stage `j`.

## Main definitions

* `Stacks.EtaleCohomology.smallEtaleEqLocus`: the open subset of an object `V` of a small étale
  site over which two sections of a sheaf agree étale locally.

## Main results

* `Stacks.EtaleCohomology.smallEtale_section_ext`: two sections agreeing on a covering sieve are
  equal.
* `Stacks.EtaleCohomology.map_eq_map_iff_range_subset_smallEtaleEqLocus`: two sections agree
  after restriction along `U ⟶ V` exactly when the image of `U` lies in the agreement locus.
* `Stacks.EtaleCohomology.exists_unitApp_eq_zero_of_isLimit`: **the injectivity half** of the
  degree zero colimit formula.

## Implementation notes

The agreement locus is the union of the images of the objects `U ⟶ V` of the small étale site on
which the two sections agree; it is open because étale morphisms are open. A morphism `U ⟶ V`
whose image lies in it is covered by the fibre products `U ×_V U'` with such `U'`, so the two
sections agree on `U` by the sheaf property. The injectivity half then follows the source: the
vanishing of the image over `V` is étale local on `V` by the local description of sections of an
inverse image, so the image of `V` in `V₀` lies in the agreement locus of the section with `0`,
and the descent of opens along a limit (Stacks 01Z4) puts the image of some `V_j` in it.

## References

* [Stacks Project, Tag 09YN](https://stacks.math.columbia.edu/tag/09YN)
* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks Project, Tag 01Z4](https://stacks.math.columbia.edu/tag/01Z4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-! ### Separatedness and the agreement locus -/

section EqLocus

variable {X : Scheme.{u}} {A : Type*} [Category* A] {FA : A → A → Type*} {CA : A → Type*}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
  [(smallEtaleTopology X).HasSheafCompose (forget A)] (G : Sheaf (smallEtaleTopology X) A)

/-- **Two sections of a sheaf on the small étale site agreeing on a covering sieve are equal**,
for coefficients in a concrete category whose forgetful functor preserves the sheaf
condition. -/
theorem smallEtale_section_ext {U : X.Etale} (S : Sieve U) (hS : S ∈ smallEtaleTopology X U)
    (s t : ToType (G.obj.obj (op U)))
    (h : ∀ ⦃U' : X.Etale⦄ (g : U' ⟶ U), S g → G.obj.map g.op s = G.obj.map g.op t) :
    s = t := by
  have hG : Presieve.IsSheaf (smallEtaleTopology X) (G.obj ⋙ forget A) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      ((sheafCompose (smallEtaleTopology X) (forget A)).obj G).property
  exact (hG S hS).isSeparatedFor.ext fun _ g hg => h g hg

/-- The open subset of `V` over which two sections `s` and `t` agree étale locally: the union of
the images of the objects `U ⟶ V` of the small étale site on which they agree. -/
def smallEtaleEqLocus (V : X.Etale) (s t : ToType (G.obj.obj (op V))) : V.left.Opens :=
  ⨆ (p : { p : Σ U : X.Etale, U ⟶ V // G.obj.map p.2.op s = G.obj.map p.2.op t }),
    ⟨Set.range p.1.2.left, p.1.2.left.isOpenMap.isOpen_range⟩

omit [(smallEtaleTopology X).HasSheafCompose (forget A)] in
/-- The image of an object on which the two sections agree lies in the agreement locus. -/
lemma range_subset_smallEtaleEqLocus {V U : X.Etale} (k : U ⟶ V) (s t : ToType (G.obj.obj (op V)))
    (h : G.obj.map k.op s = G.obj.map k.op t) :
    Set.range k.left ⊆ smallEtaleEqLocus G V s t := by
  intro x hx
  have hle := le_iSup (fun (p : { p : Σ U : X.Etale, U ⟶ V //
      G.obj.map p.2.op s = G.obj.map p.2.op t }) =>
    (⟨Set.range p.1.2.left, p.1.2.left.isOpenMap.isOpen_range⟩ : V.left.Opens)) ⟨⟨U, k⟩, h⟩
  exact hle hx

omit [(smallEtaleTopology X).HasSheafCompose (forget A)] in
/-- A point of the agreement locus lies in the image of an object on which the two sections
agree. -/
lemma exists_of_mem_smallEtaleEqLocus {V : X.Etale} (s t : ToType (G.obj.obj (op V)))
    {x : V.left} (hx : x ∈ smallEtaleEqLocus G V s t) :
    ∃ (U : X.Etale) (k : U ⟶ V), G.obj.map k.op s = G.obj.map k.op t ∧ x ∈ Set.range k.left := by
  rw [smallEtaleEqLocus, TopologicalSpace.Opens.mem_iSup] at hx
  obtain ⟨⟨⟨U, k⟩, h⟩, hx⟩ := hx
  exact ⟨U, k, h, hx⟩

/-- The square of underlying schemes of a fibre product in the small étale site. -/
lemma isPullback_smallEtale_pullback {U V W : X.Etale} (a : U ⟶ W) (b : V ⟶ W) :
    IsPullback (pullback.fst a b).left (pullback.snd a b).left a.left b.left :=
  IsPullback.map (Scheme.Etale.forget X ⋙ CategoryTheory.Over.forget X)
    (IsPullback.of_hasPullback a b)

/-- A sieve of an object of the small étale site whose members jointly cover it is covering. -/
private lemma mem_smallEtaleTopology_of_forall_mem_range {U : X.Etale} (S : Sieve U)
    (h : ∀ x : U.left, ∃ (W : X.Etale) (k : W ⟶ U), S k ∧ x ∈ Set.range k.left) :
    S ∈ smallEtaleTopology X U := by
  obtain ⟨α, Y, p, hEq⟩ := S.exists_eq_ofArrows
  rw [hEq, Scheme.ofArrows_mem_smallEtaleTopology_iff]
  refine Set.eq_univ_of_forall fun x => ?_
  obtain ⟨W, k, hk, w, rfl⟩ := h x
  obtain ⟨a, e, he⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp (hEq ▸ hk)
  refine Set.mem_iUnion.2 ⟨a, e.left w, ?_⟩
  exact (congrArg (fun φ => φ w) (congrArg (fun φ => φ.left) he)).symm

/-- **Agreement along a morphism is detected by the agreement locus.** Two sections of a
sheaf over `V` agree after restriction along `k : U ⟶ V` exactly when the image of `U` lies in
their agreement locus. -/
theorem map_eq_map_iff_range_subset_smallEtaleEqLocus {V U : X.Etale} (k : U ⟶ V)
    (s t : ToType (G.obj.obj (op V))) :
    G.obj.map k.op s = G.obj.map k.op t ↔ Set.range k.left ⊆ smallEtaleEqLocus G V s t := by
  refine ⟨range_subset_smallEtaleEqLocus G k s t, fun hk => ?_⟩
  let S : Sieve U := Sieve.generate fun U' g =>
    ∃ (U₁ : X.Etale) (k₁ : U₁ ⟶ V) (g₁ : U' ⟶ U₁),
      G.obj.map k₁.op s = G.obj.map k₁.op t ∧ g ≫ k = g₁ ≫ k₁
  have hS : S ∈ smallEtaleTopology X U := by
    refine mem_smallEtaleTopology_of_forall_mem_range S fun x => ?_
    obtain ⟨U₁, k₁, h₁, y, hy⟩ := exists_of_mem_smallEtaleEqLocus G s t (hk ⟨x, rfl⟩)
    obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := k.left) (g := k₁.left)
      x y hy.symm
    have hP := isPullback_smallEtale_pullback k k₁
    refine ⟨_, pullback.fst k k₁,
      Sieve.le_generate _ _ _ ⟨U₁, k₁, pullback.snd k k₁, h₁, pullback.condition⟩,
      hP.isoPullback.inv z, ?_⟩
    rw [← Scheme.Hom.comp_apply, hP.isoPullback_inv_fst, hz₁]
  refine smallEtale_section_ext G S hS _ _ fun U' g hg => ?_
  obtain ⟨U'', g', g'', ⟨U₁, k₁, g₁, h₁, hcomp⟩, rfl⟩ := hg
  have key : ∀ x : ToType (G.obj.obj (op V)),
      G.obj.map (g' ≫ g'').op (G.obj.map k.op x) = G.obj.map (g' ≫ g₁).op (G.obj.map k₁.op x) := by
    intro x
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← Functor.map_comp, ← op_comp, ← op_comp, Category.assoc, hcomp, Category.assoc]
  change G.obj.map (g' ≫ g'').op (G.obj.map k.op s) = G.obj.map (g' ≫ g'').op (G.obj.map k.op t)
  rw [key, key, h₁]

end EqLocus

/-! ### Base change of étale objects -/

section BaseChange

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The unit of the inverse image is natural in the object. -/
lemma smallEtalePullbackAbUnitApp_naturality (H : Sheaf (smallEtaleTopology Y) Ab.{u + 1})
    {U V : Y.Etale} (k : U ⟶ V) (h : ToType (H.obj.obj (op V))) :
    smallEtalePullbackAbUnitApp f H U (H.obj.map k.op h) =
      ((smallEtalePullbackAb f).obj H).obj.map ((smallEtaleBaseChange f).map k).op
        (smallEtalePullbackAbUnitApp f H V h) :=
  congrArg (fun φ => φ h) (((smallEtaleAdjunctionAb f).unit.app H).hom.naturality k.op)

/-- The base change of a morphism of étale objects along `f` sits in a pullback square over the
first projections. -/
lemma isPullback_smallEtaleBaseChange_map {U V : Y.Etale} (k : U ⟶ V) :
    IsPullback ((smallEtaleBaseChange f).map k).left (pullback.fst U.hom f)
      (pullback.fst V.hom f) k.left := by
  have hw : ((smallEtaleBaseChange f).map k).left ≫ pullback.snd V.hom f =
      pullback.snd U.hom f := smallEtaleBaseChange_w f ((smallEtaleBaseChange f).map k)
  have hk : k.left ≫ V.hom = U.hom := MorphismProperty.Over.w k
  refine IsPullback.of_right ?_ (smallEtaleBaseChange_map_left_fst f k)
    (IsPullback.of_hasPullback V.hom f).flip
  rw [hw, hk]
  exact (IsPullback.of_hasPullback U.hom f).flip

/-- The image of the base change of a morphism of étale objects is the preimage of its image
under the first projection. -/
lemma range_smallEtaleBaseChange_map {U V : Y.Etale} (k : U ⟶ V) :
    Set.range ((smallEtaleBaseChange f).map k).left =
      (pullback.fst V.hom f) ⁻¹' Set.range k.left := by
  have h := isPullback_smallEtaleBaseChange_map f k
  rw [← Scheme.Pullback.range_fst, ← h.isoPullback_hom_fst, Scheme.Hom.comp_base,
    TopCat.coe_comp, Set.range_comp]
  have : Function.Surjective h.isoPullback.hom.base :=
    (Scheme.Hom.homeomorph h.isoPullback.hom).surjective
  rw [this.range_eq, Set.image_univ]
  rfl

end BaseChange

/-! ### The injectivity half -/

section Limit

variable {I : Type u} [SmallCategory I] [IsCofiltered I] (D : I ⥤ Scheme.{u}) (c : Cone D)
  (hc : IsLimit c) [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]

/-- A covering sieve of an object of the small étale site is jointly surjective. -/
lemma exists_mem_range_of_mem_smallEtaleTopology {X : Scheme.{u}} {U : X.Etale} (S : Sieve U)
    (hS : S ∈ smallEtaleTopology X U) (x : U.left) :
    ∃ (U' : X.Etale) (g : U' ⟶ U), S g ∧ x ∈ Set.range g.left := by
  obtain ⟨α, Y, p, hEq⟩ := S.exists_eq_ofArrows
  have hcov := (Scheme.ofArrows_mem_smallEtaleTopology_iff p).mp (hEq ▸ hS)
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp (hcov ▸ Set.mem_univ x)
  refine ⟨Y a, p a, ?_, ha⟩
  rw [hEq]
  exact Sieve.ofArrows_mk _ _ a

include hc in
/-- **The injectivity half of the degree zero colimit formula for an inverse image.** Let
`X = lim X_i` be a cofiltered limit with affine transition morphisms, `H` an abelian sheaf on
the small étale site of a stage `X_i` and `h` a section of `H` over a quasi-compact object `V₀`.
If the image of `h` in the sections of `f_i⁻¹H` over the base change of `V₀` to `X` vanishes,
then its image in the sections of the inverse image of `H` over the base change of `V₀` to some
later stage `X_j` already vanishes. -/
theorem exists_unitApp_eq_zero_of_isLimit {i : I} (H : Sheaf (smallEtaleTopology (D.obj i)) Ab)
    (V₀ : (D.obj i).Etale) [CompactSpace V₀.left] (h : ToType (H.obj.obj (op V₀)))
    (hz : smallEtalePullbackAbUnitApp (c.π.app i) H V₀ h = 0) :
    ∃ (j : I) (f : j ⟶ i), smallEtalePullbackAbUnitApp (D.map f) H V₀ h = 0 := by
  let O := smallEtaleEqLocus H V₀ h 0
  obtain ⟨S, hS, hSz⟩ := exists_covering_of_smallEtalePullbackAb_unitApp_eq_zero (c.π.app i) H
    (𝟙 _) h (by rwa [op_id, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply])
  have hlim : Set.range (pullback.snd (c.π.app i) V₀.hom) ⊆ (O : Set V₀.left) := by
    rw [Scheme.Pullback.range_snd, ← Scheme.Pullback.range_fst]
    rintro _ ⟨x, rfl⟩
    obtain ⟨U', g, hg, u, rfl⟩ := exists_mem_range_of_mem_smallEtaleTopology S hS x
    obtain ⟨W', q, m', hm', hq⟩ := hSz g hg
    have hq' : H.obj.map q.op h = H.obj.map q.op 0 := by rw [hq, map_zero]
    refine range_subset_smallEtaleEqLocus H q h 0 hq' ⟨(m'.left ≫ pullback.fst W'.hom _) u, ?_⟩
    have e := congrArg (fun φ => φ.left ≫ pullback.fst V₀.hom (c.π.app i))
      (hm'.trans (Category.comp_id g))
    have e2 : (m'.left ≫ pullback.fst W'.hom (c.π.app i)) ≫ q.left =
        g.left ≫ pullback.fst V₀.hom (c.π.app i) :=
      (Category.assoc _ _ _).trans ((congrArg (fun ψ => m'.left ≫ ψ)
        (smallEtaleBaseChange_map_left_fst (c.π.app i) q).symm).trans
          ((Category.assoc _ _ _).symm.trans e))
    exact congrArg (fun φ => φ u) e2
  -- Descend to a stage.
  obtain ⟨j, f, hj⟩ := exists_range_pullback_snd_subset_of_isLimit D c hc
    (Z := V₀.left) V₀.hom O hlim
  refine ⟨j, f, ?_⟩
  rw [Scheme.Pullback.range_snd, ← Scheme.Pullback.range_fst] at hj
  -- The base changes of the objects on which `h` vanishes cover the base change of `V₀`.
  let T := (smallEtaleBaseChange (D.map f)).obj V₀
  let S' : Sieve T := Sieve.generate fun U' g =>
    ∃ (U : (D.obj i).Etale) (k : U ⟶ V₀), H.obj.map k.op h = H.obj.map k.op 0 ∧
      ∃ g' : U' ⟶ (smallEtaleBaseChange (D.map f)).obj U,
        g = g' ≫ (smallEtaleBaseChange (D.map f)).map k
  have hS' : S' ∈ smallEtaleTopology (D.obj j) T := by
    refine mem_smallEtaleTopology_of_forall_mem_range S' fun y => ?_
    obtain ⟨U, k, hk, u, hu⟩ := exists_of_mem_smallEtaleEqLocus H h 0 (hj ⟨y, rfl⟩)
    refine ⟨_, (smallEtaleBaseChange (D.map f)).map k,
      Sieve.le_generate _ _ _ ⟨U, k, hk, 𝟙 _, (Category.id_comp _).symm⟩, ?_⟩
    rw [range_smallEtaleBaseChange_map]
    exact ⟨u, hu⟩
  refine smallEtale_section_ext _ S' hS' _ _ fun U' g hg => ?_
  obtain ⟨U'', g₁, g₂, ⟨U, k, hk, g', rfl⟩, rfl⟩ := hg
  rw [map_zero]
  change ((smallEtalePullbackAb (D.map f)).obj H).obj.map (g₁ ≫ g' ≫ _).op
    (smallEtalePullbackAbUnitApp (D.map f) H V₀ h) = 0
  rw [op_comp, op_comp, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    ← smallEtalePullbackAbUnitApp_naturality, hk]
  simp only [map_zero]

end Limit


/-! ### Gluing sections of an abelian sheaf -/

section Glue

variable {X : Scheme.{u}} {A : Type*} [Category* A] {FA : A → A → Type*} {CA : A → Type*}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
  [(smallEtaleTopology X).HasSheafCompose (forget A)] (G : Sheaf (smallEtaleTopology X) A)

/-- **Gluing.** Sections of a sheaf on the small étale site over the members of a jointly
surjective family, which agree on the fibre products of any two members, glue to a section over
the base, for coefficients in a concrete category whose forgetful functor preserves the sheaf
condition. -/
theorem exists_glue_smallEtale {U : X.Etale} {α : Type*} (Y : α → X.Etale) (p : ∀ a, Y a ⟶ U)
    (hp : ⋃ a, Set.range (p a).left = Set.univ) (s : ∀ a, ToType (G.obj.obj (op (Y a))))
    (hs : ∀ a b, G.obj.map (pullback.fst (p a) (p b)).op (s a) =
      G.obj.map (pullback.snd (p a) (p b)).op (s b)) :
    ∃ t : ToType (G.obj.obj (op U)), ∀ a, G.obj.map (p a).op t = s a := by
  have hG : Presieve.IsSheaf (smallEtaleTopology X) (G.obj ⋙ forget A) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      ((sheafCompose (smallEtaleTopology X) (forget A)).obj G).property
  have hsf : (Presieve.ofArrows Y p).IsSheafFor (G.obj ⋙ forget A) := by
    rw [Presieve.isSheafFor_iff_generate]
    exact hG _ ((Scheme.ofArrows_mem_smallEtaleTopology_iff p).mpr hp)
  have hcomp : Presieve.Arrows.Compatible (G.obj ⋙ forget A) p s := by
    rwa [Presieve.Arrows.pullbackCompatible_iff]
  exact ((Presieve.isSheafFor_arrows_iff _ _).mp hsf s hcomp).exists

end Glue

/-! ### Comparison of sections of iterated inverse images -/

section PullbackSectionsMap

variable {X Y Z : Scheme.{u}} (g : X ⟶ Y) (f : Y ⟶ Z) (gf : X ⟶ Z) (hgf : gf = g ≫ f)

/-- Sections of `f⁻¹H` over `U` map to sections of `(gf)⁻¹H` over `U ×_Y X`: the unit of
`g⁻¹ ⊣ g_*` followed by the comparison `g⁻¹f⁻¹ ≅ (gf)⁻¹`. -/
def pullbackSectionsMap (H : Sheaf (smallEtaleTopology Z) Ab.{u + 1}) (U : Y.Etale) :
    ((smallEtalePullbackAb f).obj H).obj.obj (op U) ⟶
      ((smallEtalePullbackAb gf).obj H).obj.obj (op ((smallEtaleBaseChange g).obj U)) :=
  smallEtalePullbackAbUnitApp g ((smallEtalePullbackAb f).obj H) U ≫
    ((smallEtalePullbackAbComp' g f gf hgf).hom.app H).hom.app
      (op ((smallEtaleBaseChange g).obj U))

/-- The comparison of sections is natural in the object. -/
lemma pullbackSectionsMap_naturality (H : Sheaf (smallEtaleTopology Z) Ab.{u + 1})
    {U U' : Y.Etale} (k : U' ⟶ U) (x : ToType (((smallEtalePullbackAb f).obj H).obj.obj (op U))) :
    pullbackSectionsMap g f gf hgf H U' (((smallEtalePullbackAb f).obj H).obj.map k.op x) =
      ((smallEtalePullbackAb gf).obj H).obj.map ((smallEtaleBaseChange g).map k).op
        (pullbackSectionsMap g f gf hgf H U x) := by
  dsimp only [pullbackSectionsMap]
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    smallEtalePullbackAbUnitApp_naturality]
  exact congrArg (fun φ => φ (smallEtalePullbackAbUnitApp g _ U x))
    (((smallEtalePullbackAbComp' g f gf hgf).hom.app H).hom.naturality
      ((smallEtaleBaseChange g).map k).op)

/-- **The unit of a composite of inverse image adjunctions.** The unit of `(gf)⁻¹ ⊣ (gf)_*` is the
unit of `f⁻¹ ⊣ f_*` followed by the unit of `g⁻¹ ⊣ g_*`, the comparison of direct images and the
comparison `g⁻¹f⁻¹ ≅ (gf)⁻¹`. -/
lemma smallEtaleAdjunctionAb_unit_app_comp (H : Sheaf (smallEtaleTopology Z) Ab.{u + 1}) :
    (smallEtaleAdjunctionAb gf).unit.app H =
      (smallEtaleAdjunctionAb f).unit.app H ≫
        (smallEtalePushforwardAb f).map
          ((smallEtaleAdjunctionAb g).unit.app ((smallEtalePullbackAb f).obj H)) ≫
          (smallEtalePushforwardAbComp' g f gf hgf).hom.app _ ≫
            (smallEtalePushforwardAb gf).map
              ((smallEtalePullbackAbComp' g f gf hgf).hom.app H) := by
  have key := leftAdjointCompIso_inv_homEquiv_symm (smallEtaleAdjunctionAb f)
    (smallEtaleAdjunctionAb g) (smallEtaleAdjunctionAb gf)
    (smallEtalePushforwardAbComp' g f gf hgf)
    ((smallEtaleAdjunctionAb f).unit.app H)
    ((smallEtaleAdjunctionAb g).unit.app ((smallEtalePullbackAb f).obj H))
  rw [← smallEtalePullbackAbComp'_eq_leftAdjointCompIso] at key
  simp only [Functor.id_obj, Adjunction.homEquiv_counit, Adjunction.left_triangle_components,
    CategoryTheory.Functor.map_id, Category.comp_id] at key
  rw [← Adjunction.homEquiv_counit] at key
  have key2 := congrArg ((smallEtaleAdjunctionAb gf).homEquiv _ _) key
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit] at key2
  have key3 := (congrArg (fun φ => (smallEtaleAdjunctionAb gf).unit.app H ≫
    (smallEtalePushforwardAb gf).map φ) (Category.comp_id _).symm).trans key2
  calc (smallEtaleAdjunctionAb gf).unit.app H
      = (smallEtaleAdjunctionAb gf).unit.app H ≫ (smallEtalePushforwardAb gf).map
          ((smallEtalePullbackAbComp' g f gf hgf).inv.app H ≫
            (smallEtalePullbackAbComp' g f gf hgf).hom.app H) := by
        rw [Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
        exact (Category.comp_id _).symm
    _ = _ := by
        rw [CategoryTheory.Functor.map_comp, ← Category.assoc]
        refine (congrArg (fun φ => φ ≫ (smallEtalePushforwardAb gf).map
          ((smallEtalePullbackAbComp' g f gf hgf).hom.app H)) key3).trans ?_
        simp only [Category.assoc]

/-- **The unit of a composite adjunction, on sections.** The comparison of sections carries the
image of a section of `H` under the unit of `f⁻¹ ⊣ f_*` to its image under the unit of
`(gf)⁻¹ ⊣ (gf)_*`, read through the identification of the iterated base change. -/
lemma pullbackSectionsMap_unitApp (H : Sheaf (smallEtaleTopology Z) Ab.{u + 1}) (V₀ : Z.Etale)
    (h : ToType (H.obj.obj (op V₀))) :
    ((smallEtalePullbackAb gf).obj H).obj.map
        ((smallEtaleBaseChangeComp' g f gf hgf).hom.app V₀).op
        (pullbackSectionsMap g f gf hgf H ((smallEtaleBaseChange f).obj V₀)
          (smallEtalePullbackAbUnitApp f H V₀ h)) =
      smallEtalePullbackAbUnitApp gf H V₀ h := by
  have hu := congrArg (fun φ => φ.hom.app (op V₀) h)
    (smallEtaleAdjunctionAb_unit_app_comp g f gf hgf H)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply] at hu
  refine Eq.trans ?_ hu.symm
  have he := smallEtalePushforwardComp'_hom_app_hom_app g f gf hgf Ab.{u + 1}
    ((smallEtalePullbackAb g).obj ((smallEtalePullbackAb f).obj H)) (op V₀)
  have hn := congrArg (fun φ => φ (smallEtalePullbackAbUnitApp g ((smallEtalePullbackAb f).obj H)
      ((smallEtaleBaseChange f).obj V₀) (smallEtalePullbackAbUnitApp f H V₀ h)))
    (((smallEtalePullbackAbComp' g f gf hgf).hom.app H).hom.naturality
      ((smallEtaleBaseChangeComp' g f gf hgf).hom.app V₀).op)
  simp only [ConcreteCategory.comp_apply] at hn
  refine hn.symm.trans ?_
  exact congrArg (fun z => ((smallEtalePullbackAbComp' g f gf hgf).hom.app H).hom.app _ z)
    (congrArg (fun φ => φ (smallEtalePullbackAbUnitApp g ((smallEtalePullbackAb f).obj H)
      ((smallEtaleBaseChange f).obj V₀) (smallEtalePullbackAbUnitApp f H V₀ h))) he.symm)

end PullbackSectionsMap

end Stacks.EtaleCohomology

end
