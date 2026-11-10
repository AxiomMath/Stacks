module

public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.AlgebraicTopology.SimplicialObject.Coskeletal
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import Mathlib.CategoryTheory.Subfunctor.Image
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicTopology.SimplicialObject.ChainHomotopy
public import StacksFrontier.AlgebraicTopology.SimplicialSet.TrivialKanFibration.CechNerve
public import StacksFrontier.CategoryTheory.Sites.CechNerveHomology

/-!
# Acyclicity of a coskeletal morphism of simplicial presheaves

Let `C` be a site with Grothendieck topology `J` and let `f : L ⟶ K` be a morphism of
simplicial presheaves of sets on `C`.  Fix `n : ℕ` and assume that

1. `f` is an isomorphism in every degree `< n`,
2. `f` is locally surjective in degree `n`,
3. the canonical maps `L ⟶ cosk_n sk_n L` and `K ⟶ cosk_n sk_n K` are isomorphisms.

This file proves that `f` then induces an isomorphism on every homology sheaf
`H_i(L) ⟶ H_i(K)` of Stacks Project, Tag 01GB, which is Stacks Project, Tag 01GD.

The homology sheaves are the ones defined in
`StacksFrontier.CategoryTheory.Sites.CechNerveHomology`, namely
`CategoryTheory.SimplicialObject.sheafHomology`, the homology of the alternating face map
complex of the degreewise free abelian sheaf `s(**Z**_K^♯)`.

## Main definitions

* `CategoryTheory.SimplicialObject.coskeletalImageDegree` is, in each simplicial degree `m`,
  the subfunctor of `K_m` cut out by the condition that every restriction to a degree `≤ n`
  lies in the image of `f`; `CategoryTheory.SimplicialObject.coskeletalImage` assembles these
  into a simplicial subpresheaf `K'` of `K`.
* `CategoryTheory.SimplicialObject.coskeletalImageι` and
  `CategoryTheory.SimplicialObject.toCoskeletalImage` are the two halves `K' ⟶ K` and
  `L ⟶ K'` of the resulting factorisation of `f`, and
  `CategoryTheory.SimplicialObject.liftCoskeletalImage` is the universal property of `K'`
  used to invert the unit of the coskeleton adjunction at `K'`.

## Main results

* `CategoryTheory.SimplicialObject.isIso_sheafHomologyFunctor_map_of_coskeletal` is Tag 01GD.
* `CategoryTheory.SimplicialObject.isIso_sheafHomologyFunctor_map_of_surjective_of_coskeletal`
  is the special case in which `f` is surjective on sections in degree `n`: there the
  comparison is checked one object of `C` at a time, where it is the statement that a trivial
  Kan fibration of simplicial sets induces a quasi-isomorphism of free abelian complexes
  (`SSet.quasiIso_alternatingFaceMapComplex_map_free_of_coskeletal`).
* `CategoryTheory.SimplicialObject.isIso_sheafHomologyFunctor_map_of_degreewise_W` is the
  complementary special case: a morphism which becomes an isomorphism after sheafification in
  every degree induces isomorphisms on homology sheaves.
* `CategoryTheory.Presheaf.W_ι_of_isLocallySurjective`: a locally surjective subpresheaf
  inclusion becomes an isomorphism after sheafification.
* `CategoryTheory.GrothendieckTopology.iInf_covering`: a finite infimum of covering sieves is
  a covering sieve.

## Implementation notes

The universes are those of `CechNerveHomology`: the site is `C : Type u` with
`Category.{v} C`, and the presheaves of sets take values in `Type w` with `w` *independent*
of `u` and `v`.  Nothing here fixes `w = max u v`; in particular sheafification of
type-valued presheaves is never used, and the only sheafification hypothesis is the one the
statement of Tag 01GB needs, `HasSheafify J AddCommGrpCat.{w}`.  That hypothesis carries left
exactness of `presheafToSheaf` as part of its definition, which is what lets the comparison be
checked before sheafifying.  The universe generality is forced by the statement, not chosen:
the simplicial presheaves are arbitrary.

Surjectivity after sheafification is expressed by Mathlib's
`CategoryTheory.Presheaf.IsLocallySurjective`, the intrinsic local-surjectivity condition on
the map of presheaves, rather than by surjectivity of a map of sheaves of sets; this is again
what keeps `w` free, since the sheafification of a `Type w`-valued presheaf is unavailable.
The canonical maps to the coskeleta are the units of the truncation–coskeleton adjunction
`CategoryTheory.SimplicialObject.coskAdj`, and "`L` is `n`-coskeletal" is the assertion that
that unit is an isomorphism.

The proof follows the source: `f` is factored as `L ⟶ K' ⟶ K` through the simplicial
subpresheaf `K'` of degreewise images-through-degree-`n`.  The first half is surjective on
sections in degrees `≤ n` and still has coskeletal source and target, so it is treated by the
trivial Kan fibration argument objectwise.  The second half is locally surjective in every
degree and is a subpresheaf inclusion, hence inverted by sheafification, so the free abelian
sheaf functor inverts it degreewise.  Taking `K'` to be cut out by the image condition in
*all* degrees `≤ n` simultaneously — rather than only in degree `n`, as the source's
`cosk_n U` does — is what makes it a simplicial subobject of `K` with no coskeleton
computation; its `n`-coskeletality is then obtained from that of `K` by
`isIso_coskAdj_unit_app_coskeletalImage`, whose inverse is built out of the counit of the
adjunction.

The finiteness of `SimplexCategory`'s hom-sets is used in
`isLocallySurjective_coskeletalImageι_app`: a simplex of `K_m` has only finitely many
restrictions to degrees `≤ n`, so the finitely many sieves on which these restrictions lift
through `f` can be intersected, which is `GrothendieckTopology.iInf_covering`.

## References

* [Stacks Project, Tag 01GB](https://stacks.math.columbia.edu/tag/01GB)
* [Stacks Project, Tag 01GC](https://stacks.math.columbia.edu/tag/01GC)
* [Stacks Project, Tag 01GD](https://stacks.math.columbia.edu/tag/01GD)
-/

@[expose] public section

open CategoryTheory Opposite

universe w v u

/- **Stacks Project, Tag 01GB** is the homology of a simplicial presheaf: the homology of the
alternating face map complex of its degreewise free abelian sheaf.  That object is already in
the library, as `CategoryTheory.SimplicialObject.sheafHomology` in
`StacksFrontier.CategoryTheory.Sites.CechNerveHomology`, together with the complex
`CategoryTheory.SimplicialObject.freeAbelianSheafComplexFunctor` and the functor
`CategoryTheory.SimplicialObject.sheafHomologyFunctor` it is the object part of.  The tag is
recorded here rather than duplicating the definition. -/
add_to_stacks 01GB CategoryTheory.SimplicialObject.sheafHomology

namespace CategoryTheory

open Limits _root_.CategoryTheory.Functor AlgebraicTopology

namespace GrothendieckTopology

variable {C : Type u} [Category.{v} C]

/-- A finite infimum of covering sieves is a covering sieve.  This is
`GrothendieckTopology.intersection_covering` for a finite family rather than for two sieves. -/
@[sga "3 IV 4.2.1" "T′5 with F representable", sga "4 II 1.1.1"]
theorem iInf_covering (J : GrothendieckTopology C) {X : C} {I : Type*} [Finite I]
    (S : I → Sieve X) (hS : ∀ i, S i ∈ J X) : (⨅ i, S i) ∈ J X := by
  classical
  let := Fintype.ofFinite I
  have h (t : Finset I) : t.inf S ∈ J X := by
    induction t using Finset.induction_on with
    | empty => simp
    | @insert i t hi ht =>
      rw [Finset.inf_insert]
      exact J.intersection_covering (hS i) ht
  simpa only [Finset.inf_eq_iInf, Finset.mem_univ, iInf_true] using h Finset.univ

end GrothendieckTopology

namespace Presheaf

variable {C : Type u} [Category.{v} C]

/-- A locally surjective subpresheaf inclusion becomes an isomorphism after sheafification.

Unlike `CategoryTheory.Presheaf.W_range_ι_of_isLocallySurjective`, which is about the image
subpresheaf of a locally surjective morphism, this is stated for an arbitrary subfunctor whose
inclusion is locally surjective.  The subpresheaf sheafification `Subfunctor.sheafify` supplies
the universal property, so no sheafification of type-valued presheaves is needed and the
universe `w` of the presheaf stays free. -/
theorem W_ι_of_isLocallySurjective (J : GrothendieckTopology C) {F : Cᵒᵖ ⥤ Type w}
    (S : Subfunctor F) [Presheaf.IsLocallySurjective J S.ι] : J.W S.ι := by
  have htop : S.sheafify J = ⊤ := by
    apply top_unique
    intro X s _
    change S.sieveOfSection s ∈ J X.unop
    have he : S.sieveOfSection s = Presheaf.imageSieve S.ι s := by
      ext Y a
      constructor
      · exact fun h => ⟨⟨_, h⟩, rfl⟩
      · rintro ⟨t, ht⟩
        change t.1 = F.map a.op s at ht
        change F.map a.op s ∈ S.obj (op Y)
        exact ht ▸ t.2
    rw [he]
    exact Presheaf.imageSieve_mem J _ _
  have hiso : IsIso (S.sheafify J).ι := (Subfunctor.eq_top_iff_isIso _).1 htop
  intro G hG
  have hg : Presieve.IsSheaf J G := (isSheaf_iff_isSheaf_of_type J G).1 hG
  let a : S.toFunctor ⟶ (S.sheafify J).toFunctor := Subfunctor.homOfLe (S.le_sheafify J)
  have ha : a ≫ (S.sheafify J).ι = S.ι := Subfunctor.homOfLe_ι _
  constructor
  · intro b c h
    apply (cancel_epi (S.sheafify J).ι).1
    apply S.to_sheafify_lift_unique hg
    change a ≫ ((S.sheafify J).ι ≫ b) = a ≫ ((S.sheafify J).ι ≫ c)
    simpa only [← Category.assoc, ha] using h
  · intro b
    refine ⟨inv (S.sheafify J).ι ≫ S.sheafifyLift b hg, ?_⟩
    change S.ι ≫ _ = b
    rw [← ha, Category.assoc, IsIso.hom_inv_id_assoc]
    exact S.to_sheafifyLift b hg

end Presheaf

namespace SimplicialObject

variable {C : Type u} [Category.{v} C]

/-- If a simplicial object of a presheaf category is `n`-coskeletal, then so is its value at
each object of the site: evaluation preserves the right Kan extension computing `cosk_n`. -/
theorem isIso_coskAdj_unit_app_comp_evaluation
    (L : SimplicialObject (Cᵒᵖ ⥤ Type w)) (n : ℕ)
    (hL : IsIso ((SimplicialObject.coskAdj n).unit.app L)) (X : Cᵒᵖ) :
    IsIso ((SimplicialObject.coskAdj n).unit.app
      (L ⋙ (evaluation _ _).obj X)) := by
  have : L.IsCoskeletal n := (SimplicialObject.isCoskeletal_iff_isIso L n).2 hL
  apply (SimplicialObject.isCoskeletal_iff_isIso _ n).1
  constructor
  exact Functor.PreservesRightKanExtension.preserves
    (G := (evaluation Cᵒᵖ (Type w)).obj X) L
    (𝟙 ((SimplexCategory.Truncated.inclusion n).op ⋙ L))

end SimplicialObject

end CategoryTheory

namespace SSet

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicTopology

/-- A morphism of simplicial sets which is bijective in degrees below `n`, surjective in
degree `n`, and whose source and target are `n`-coskeletal is a trivial Kan fibration
(`SSet.trivialKanFibrations_of_coskeletal`), hence a homotopy equivalence; applying the free
abelian group functor degreewise therefore yields a quasi-isomorphism of alternating face map
complexes. -/
theorem quasiIso_alternatingFaceMapComplex_map_free_of_coskeletal
    {L K : SSet.{w}} (f : L ⟶ K) (n : ℕ)
    (h_lt : ∀ j : ℕ, j < n → Function.Bijective (f.app (op (SimplexCategory.mk j))))
    (h_surj : Function.Surjective (f.app (op (SimplexCategory.mk n))))
    (hL : IsIso ((SimplicialObject.coskAdj n).unit.app L))
    (hK : IsIso ((SimplicialObject.coskAdj n).unit.app K)) :
    QuasiIso
      ((alternatingFaceMapComplex _).map (whiskerRight f AddCommGrpCat.free)) := by
  obtain ⟨g, ⟨h₁⟩, ⟨h₂⟩⟩ := SSet.trivialKanFibrations_isHomotopyEquiv f
    (SSet.trivialKanFibrations_of_coskeletal f n h_lt h_surj hK hL)
  apply homotopyEquivalences_le_quasiIso
  apply homotopyEquivalences_alternatingFaceMapComplex_map
  refine ⟨whiskerRight g AddCommGrpCat.free, ?_, ?_⟩
  · apply Relation.EqvGen.rel
    simpa using Nonempty.intro (h₁.toSimplicialObjectHomotopy.whiskerRight AddCommGrpCat.free)
  · apply Relation.EqvGen.rel
    simpa using Nonempty.intro (h₂.toSimplicialObjectHomotopy.whiskerRight AddCommGrpCat.free)

end SSet

namespace CategoryTheory.SimplicialObject

open Limits _root_.CategoryTheory.Functor AlgebraicTopology

variable {C : Type u} [Category.{v} C]

/-- A morphism of simplicial presheaves of sets which is an isomorphism in degrees below `n`,
*surjective on sections* in degree `n`, and whose source and target are `n`-coskeletal induces
an isomorphism on every homology sheaf.

This is the form of Tag 01GD in which no sheafification is needed to see the surjectivity: the
comparison is checked one object of `C` at a time, where it is
`SSet.quasiIso_alternatingFaceMapComplex_map_free_of_coskeletal`. -/
theorem isIso_sheafHomologyFunctor_map_of_surjective_of_coskeletal
    (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{w}]
    {L K : SimplicialObject (Cᵒᵖ ⥤ Type w)} (f : L ⟶ K) (n i : ℕ)
    (h_lt : ∀ j : ℕ, j < n → IsIso (f.app (op (SimplexCategory.mk j))))
    (h_surj : ∀ X, Function.Surjective ((f.app (op (SimplexCategory.mk n))).app X))
    (hL : IsIso ((SimplicialObject.coskAdj n).unit.app L))
    (hK : IsIso ((SimplicialObject.coskAdj n).unit.app K)) :
    IsIso ((sheafHomologyFunctor J i).map f) := by
  let g := whiskerRight f ((whiskeringRight _ _ _).obj AddCommGrpCat.free)
  have hg : QuasiIso ((alternatingFaceMapComplex _).map g) := by
    rw [HomologicalComplex.quasiIso_iff_evaluation]
    intro X
    have h := SSet.quasiIso_alternatingFaceMapComplex_map_free_of_coskeletal
      (whiskerRight f ((evaluation _ _).obj X)) n
      (fun j hj => by
        have := h_lt j hj
        exact (isIso_iff_bijective _).1 (inferInstanceAs (IsIso ((f.app _).app X))))
      (h_surj X) (isIso_coskAdj_unit_app_comp_evaluation L n hL X)
      (isIso_coskAdj_unit_app_comp_evaluation K n hK X)
    change QuasiIso ((alternatingFaceMapComplex _ ⋙
      ((evaluation Cᵒᵖ AddCommGrpCat.{w}).obj X).mapHomologicalComplex _).map g)
    rwa [map_alternatingFaceMapComplex]
  have hc : QuasiIso ((freeAbelianSheafComplexFunctor J).map f) := by
    have ht := HomologicalComplex.quasiIso_map_of_preservesHomology
      ((alternatingFaceMapComplex _).map g) (presheafToSheaf J AddCommGrpCat.{w})
    change QuasiIso ((alternatingFaceMapComplex _ ⋙
      (presheafToSheaf J AddCommGrpCat.{w}).mapHomologicalComplex _).map g) at ht
    rwa [map_alternatingFaceMapComplex] at ht
  exact (quasiIsoAt_iff_isIso_homologyMap _ i).1 (hc.quasiIsoAt i)

/-- The simplices whose restrictions in every degree at most `n` belong to the image of `f`. -/
def coskeletalImageDegree
    {L K : SimplicialObject (Cᵒᵖ ⥤ Type w)} (f : L ⟶ K) (n : ℕ)
    (m : SimplexCategoryᵒᵖ) : Subfunctor (K.obj m) where
  obj X := {s | ∀ (j : Fin (n + 1)) (θ : m ⟶ op (SimplexCategory.mk j)),
    (K.map θ).app X s ∈ Set.range ((f.app (op (SimplexCategory.mk j))).app X)}
  map := by
    intro X Y a s hs j θ
    obtain ⟨t, ht⟩ := hs j θ
    refine ⟨(L.obj _).map a t, ?_⟩
    rw [NatTrans.naturality_apply, ht, NatTrans.naturality_apply]

/-- The simplicial subpresheaf obtained by imposing the image condition through degree `n`.

Imposing it in all degrees `≤ n` at once, rather than only in degree `n`, is what makes this a
simplicial subobject of `K`; it is the subpresheaf `K'` of the proof of Tag 01GD. -/
def coskeletalImage
    {L K : SimplicialObject (Cᵒᵖ ⥤ Type w)} (f : L ⟶ K) (n : ℕ) :
    SimplicialObject (Cᵒᵖ ⥤ Type w) where
  obj m := (coskeletalImageDegree f n m).toFunctor
  map {m m'} θ :=
    { app X := ↾fun s => ⟨(K.map θ).app X s.1, fun j φ => by
        simpa using s.2 j (θ ≫ φ)⟩
      naturality := by
        intro X Y a
        ext s
        apply Subtype.ext
        exact NatTrans.naturality_apply (K.map θ) a s.1 }
  map_id m := by ext X s; apply Subtype.ext; simp
  map_comp θ φ := by ext X s; apply Subtype.ext; simp

/-- The inclusion of `CategoryTheory.SimplicialObject.coskeletalImage` into `K`. -/
def coskeletalImageι
    {L K : SimplicialObject (Cᵒᵖ ⥤ Type w)} (f : L ⟶ K) (n : ℕ) :
    coskeletalImage f n ⟶ K where
  app m := (coskeletalImageDegree f n m).ι

/-- The factorisation of `f` through `CategoryTheory.SimplicialObject.coskeletalImage`: every
simplex in the image of `f` satisfies the image condition in all degrees. -/
def toCoskeletalImage
    {L K : SimplicialObject (Cᵒᵖ ⥤ Type w)} (f : L ⟶ K) (n : ℕ) :
    L ⟶ coskeletalImage f n where
  app m := Subfunctor.lift (f.app m) (by
    intro X s hs j θ
    obtain ⟨t, rfl⟩ := hs
    refine ⟨(L.map θ).app X t, ?_⟩
    exact congrFun (congrArg (fun g => (g.app X).hom) (f.naturality θ)) t)
  naturality := by
    intro m m' θ
    ext X s
    apply Subtype.ext
    exact congrFun (congrArg (fun g => (g.app X).hom) (f.naturality θ)) s

/-- In every degree `j ≤ n` the factorisation `L ⟶ K'` of `f` through the image condition is
surjective on sections: the condition applied to the identity of degree `j` says exactly that a
simplex of `K'_j` lies in the image of `f_j`. -/
theorem surjective_toCoskeletalImage_app
    {L K : SimplicialObject (Cᵒᵖ ⥤ Type w)} (f : L ⟶ K) (n : ℕ)
    (j : ℕ) (hj : j ≤ n) (X : Cᵒᵖ) :
    Function.Surjective (((toCoskeletalImage f n).app (op (SimplexCategory.mk j))).app X) := by
  intro s
  obtain ⟨t, ht⟩ := s.2 ⟨j, by omega⟩ (𝟙 _)
  refine ⟨t, Subtype.ext ?_⟩
  change ((f.app (op (SimplexCategory.mk j))).app X) t = s.1
  simpa using ht

/-- In a degree `j ≤ n` in which `f` is an isomorphism, so is the factorisation `L ⟶ K'`:
it is injective because `f_j` is, and surjective by
`CategoryTheory.SimplicialObject.surjective_toCoskeletalImage_app`. -/
theorem isIso_toCoskeletalImage_app
    {L K : SimplicialObject (Cᵒᵖ ⥤ Type w)} (f : L ⟶ K) (n : ℕ)
    (j : ℕ) (hj : j ≤ n) [IsIso (f.app (op (SimplexCategory.mk j)))] :
    IsIso ((toCoskeletalImage f n).app (op (SimplexCategory.mk j))) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  rw [isIso_iff_bijective]
  refine ⟨?_, surjective_toCoskeletalImage_app f n j hj X⟩
  intro a b h
  exact ((isIso_iff_bijective ((f.app (op (SimplexCategory.mk j))).app X)).1
    (inferInstanceAs (IsIso ((f.app _).app X)))).injective (congrArg Subtype.val h)

/-- A map whose components through degree `n` land in the image of `f` factors through the
simplicial subpresheaf `CategoryTheory.SimplicialObject.coskeletalImage`.

This is the universal property of `K'` which is needed: the condition is only imposed in
degrees `≤ n`, but a map satisfying it there automatically satisfies it in all degrees, by
naturality. -/
def liftCoskeletalImage
    {L K T : SimplicialObject (Cᵒᵖ ⥤ Type w)} (f : L ⟶ K) (n : ℕ)
    (β : T ⟶ K)
    (hβ : ∀ (j : ℕ), j ≤ n → ∀ (X : Cᵒᵖ) (t : (T.obj (op (SimplexCategory.mk j))).obj X),
      (β.app (op (SimplexCategory.mk j))).app X t ∈
        Set.range ((f.app (op (SimplexCategory.mk j))).app X)) :
    T ⟶ coskeletalImage f n where
  app m := Subfunctor.lift (β.app m) (by
    intro X s hs j θ
    obtain ⟨t, rfl⟩ := hs
    have e := congrFun (congrArg (fun g => (g.app X).hom) (β.naturality θ)) t
    change (K.map θ).app X ((β.app m).app X t) ∈ _
    dsimp at e
    rw [← e]
    exact hβ j (by omega) X ((T.map θ).app X t))
  naturality := by
    intro m m' θ
    ext X s
    apply Subtype.ext
    exact congrFun (congrArg (fun g => (g.app X).hom) (β.naturality θ)) s

/-- The image condition through degree `n` defines an `n`-coskeletal subpresheaf of an
`n`-coskeletal target.  The inverse to the unit is induced by the counit on truncations:
`cosk_n sk_n K' ⟶ K` lands in `K'` because a simplex of `cosk_n sk_n K'` restricts, in each
degree `≤ n`, to a simplex of `K'`. -/
theorem isIso_coskAdj_unit_app_coskeletalImage
    {L K : SimplicialObject (Cᵒᵖ ⥤ Type w)} (f : L ⟶ K) (n : ℕ)
    (hK : IsIso ((SimplicialObject.coskAdj n).unit.app K)) :
    IsIso ((SimplicialObject.coskAdj n).unit.app (coskeletalImage f n)) := by
  let S := coskeletalImage f n
  let a := coskeletalImageι f n
  let η := (SimplicialObject.coskAdj (C := Cᵒᵖ ⥤ Type w) n).unit
  let R := SimplicialObject.cosk (C := Cᵒᵖ ⥤ Type w) n
  let T := SimplicialObject.truncation (C := Cᵒᵖ ⥤ Type w) n
  let ε := (SimplicialObject.coskAdj (C := Cᵒᵖ ⥤ Type w) n).counit
  have hm : ∀ m, Mono (a.app m) := fun m => inferInstanceAs (Mono (coskeletalImageDegree f n m).ι)
  have : Mono a := NatTrans.mono_of_mono_app a
  have : PreservesLimitsOfSize.{0, 0} (SimplicialObject.Truncated.cosk (C := Cᵒᵖ ⥤ Type w) n) :=
    (SimplicialObject.coskAdj n).rightAdjoint_preservesLimits
  have : Mono (T.map a) := (NatTrans.mono_iff_mono_app _).2 fun q => hm _
  have : Mono (R.map a) :=
    inferInstanceAs (Mono ((SimplicialObject.Truncated.cosk n).map (T.map a)))
  let β : R.obj S ⟶ K := R.map a ≫ inv (η.app K)
  have htr : T.map β = ε.app (T.obj S) ≫ T.map a := by
    dsimp [β]
    rw [T.map_comp]
    have hε : ε.app (T.obj K) = inv (T.map (η.app K)) := by
      apply (cancel_epi (T.map (η.app K))).1
      rw [IsIso.hom_inv_id]
      exact (SimplicialObject.coskAdj n).left_triangle_components K
    rw [T.map_inv, ← hε]
    exact ε.naturality (T.map a)
  have hβ (j : ℕ) (hj : j ≤ n) (X : Cᵒᵖ)
      (t : ((R.obj S).obj (op (SimplexCategory.mk j))).obj X) :
      (β.app (op (SimplexCategory.mk j))).app X t ∈
        Set.range ((f.app (op (SimplexCategory.mk j))).app X) := by
    let q : (SimplexCategory.Truncated n)ᵒᵖ := op ⟨SimplexCategory.mk j, hj⟩
    have e := congrFun (congrArg (fun g => (g.app X).hom) (congr_app htr q)) t
    let s := ((ε.app (T.obj S)).app q).app X t
    change (β.app (op (SimplexCategory.mk j))).app X t = s.1 at e
    rw [e]
    simpa using s.2 ⟨j, by omega⟩ (𝟙 _)
  let b := liftCoskeletalImage f n β hβ
  have hb : b ≫ a = β := rfl
  have hn : η.app S ≫ R.map a = a ≫ η.app K := (η.naturality a).symm
  refine ⟨⟨b, ?_, ?_⟩⟩
  · apply (cancel_mono a).1
    rw [Category.assoc, hb]
    dsimp [β]
    rw [← Category.assoc, hn, Category.assoc, IsIso.hom_inv_id, Category.comp_id,
      Category.id_comp]
  · apply (cancel_mono (R.map a)).1
    rw [Category.assoc, hn, ← Category.assoc, hb]
    dsimp [β]
    simp

/-- Each simplex has only finitely many restrictions in degrees at most `n`, so their local
lifting conditions hold simultaneously on a covering sieve; hence the inclusion of the image
condition is locally surjective in every simplicial degree. -/
theorem isLocallySurjective_coskeletalImageι_app
    (J : GrothendieckTopology C)
    {L K : SimplicialObject (Cᵒᵖ ⥤ Type w)} (f : L ⟶ K) (n : ℕ)
    (h : ∀ j : ℕ, j ≤ n → Presheaf.IsLocallySurjective J (f.app (op (SimplexCategory.mk j))))
    (m : SimplexCategoryᵒᵖ) :
    Presheaf.IsLocallySurjective J ((coskeletalImageι f n).app m) := by
  classical
  have (j : Fin (n + 1)) : Finite (m ⟶ op (SimplexCategory.mk j)) :=
    Finite.of_injective (fun θ : m ⟶ op (SimplexCategory.mk j) => θ.unop)
      (fun _ _ h => Quiver.Hom.unop_inj h)
  constructor
  intro X s
  let I := Σ j : Fin (n + 1), m ⟶ op (SimplexCategory.mk j)
  let U : I → Sieve X := fun q =>
    Presheaf.imageSieve (f.app (op (SimplexCategory.mk q.1))) ((K.map q.2).app (op X) s)
  have hU : ∀ q, U q ∈ J X := by
    intro q
    have := h q.1 (by omega)
    exact Presheaf.imageSieve_mem J _ _
  apply J.superset_covering (S := ⨅ q, U q) _ (J.iInf_covering U hU)
  intro Y a ha
  refine ⟨⟨(K.obj m).map a.op s, ?_⟩, rfl⟩
  intro j θ
  have hq : U ⟨j, θ⟩ a := (iInf_le U ⟨j, θ⟩) a ha
  change ∃ t, (f.app (op (SimplexCategory.mk j))).app (op Y) t =
    (K.obj (op (SimplexCategory.mk j))).map a.op ((K.map θ).app (op X) s) at hq
  change ∃ t, (f.app (op (SimplexCategory.mk j))).app (op Y) t = _
  simpa only [NatTrans.naturality_apply] using hq

/-- A morphism of simplicial presheaves of sets which becomes an isomorphism after
sheafification in every degree induces an isomorphism on every homology sheaf: the free abelian
sheaf functor inverts such a morphism degreewise, so the induced map of complexes is an
isomorphism. -/
theorem isIso_sheafHomologyFunctor_map_of_degreewise_W
    (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{w}]
    {L K : SimplicialObject (Cᵒᵖ ⥤ Type w)} (f : L ⟶ K)
    (hf : ∀ m, J.W (f.app m)) (i : ℕ) :
    IsIso ((sheafHomologyFunctor J i).map f) := by
  let A : (Cᵒᵖ ⥤ Type w) ⥤ Sheaf J AddCommGrpCat.{w} :=
    (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙ presheafToSheaf J _
  have : IsIso (whiskerRight f A) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro m
    change IsIso ((presheafToSheaf J AddCommGrpCat.{w}).map
      (whiskerRight (f.app m) AddCommGrpCat.free))
    rw [← J.W_iff]
    exact J.W_of_preservesSheafification AddCommGrpCat.free _ (hf m)
  exact inferInstanceAs (IsIso (((alternatingFaceMapComplex _ ⋙
    HomologicalComplex.homologyFunctor _ _ i)).map (whiskerRight f A)))

/-- **Stacks Project, Tag 01GD.** A morphism between `n`-coskeletal simplicial
presheaves which is an isomorphism in degrees below `n` and locally surjective
in degree `n` induces an isomorphism on every homology sheaf. -/
@[stacks 01GD, sga "4 V 7.2.1" "homology iso"]
theorem isIso_sheafHomologyFunctor_map_of_coskeletal
    (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{w}]
    {L K : SimplicialObject (Cᵒᵖ ⥤ Type w)} (f : L ⟶ K) (n i : ℕ)
    (h_lt : ∀ j : ℕ, j < n → IsIso (f.app (op (SimplexCategory.mk j))))
    (h_surjective :
      Presheaf.IsLocallySurjective J (f.app (op (SimplexCategory.mk n))))
    (hL : IsIso ((SimplicialObject.coskAdj n).unit.app L))
    (hK : IsIso ((SimplicialObject.coskAdj n).unit.app K)) :
    IsIso ((sheafHomologyFunctor J i).map f) := by
  have hsurj (j : ℕ) (hj : j ≤ n) :
      Presheaf.IsLocallySurjective J (f.app (op (SimplexCategory.mk j))) := by
    obtain rfl | hj := eq_or_lt_of_le hj
    · exact h_surjective
    · have := h_lt j hj
      infer_instance
  have h₁ : IsIso ((sheafHomologyFunctor J i).map (toCoskeletalImage f n)) :=
    isIso_sheafHomologyFunctor_map_of_surjective_of_coskeletal J (toCoskeletalImage f n) n i
      (fun j hj => by
        have := h_lt j hj
        exact isIso_toCoskeletalImage_app f n j (by omega))
      (surjective_toCoskeletalImage_app f n n le_rfl)
      hL (isIso_coskAdj_unit_app_coskeletalImage f n hK)
  have h₂ : IsIso ((sheafHomologyFunctor J i).map (coskeletalImageι f n)) :=
    isIso_sheafHomologyFunctor_map_of_degreewise_W J (coskeletalImageι f n) (fun m => by
      have : Presheaf.IsLocallySurjective J (coskeletalImageDegree f n m).ι :=
        isLocallySurjective_coskeletalImageι_app J f n hsurj m
      exact Presheaf.W_ι_of_isLocallySurjective J (coskeletalImageDegree f n m)) i
  change IsIso ((sheafHomologyFunctor J i).map
    (toCoskeletalImage f n ≫ coskeletalImageι f n))
  rw [Functor.map_comp]
  infer_instance

end CategoryTheory.SimplicialObject
