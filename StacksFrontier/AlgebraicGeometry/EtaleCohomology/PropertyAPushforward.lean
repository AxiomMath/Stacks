module

public import Mathlib.CategoryTheory.Sites.EpiMono
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeContinuous
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Descent.PropertyB
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PropertyA
public import StacksFrontier.CategoryTheory.Sites.Topos.AbelianPushforwardFaithful
public import StacksFrontier.CategoryTheory.Sites.Topos.ExactnessOfMorphism

/-!
# Direct image of abelian sheaves along a morphism with property (A)

Let `f : X ⟶ Y` be a morphism of schemes with property (A): every point of every scheme étale
over `X` is reached from one piece of a disjoint union decomposition of an étale base change of
`f`. Direct image along the induced morphism of small étale sites is then very close to being an
equivalence on abelian sheaves: it reflects injections and surjections, the counit of the
inverse-image/direct-image adjunction is surjective, and direct image is faithful.

The reason is that property (A) makes the sections of an abelian sheaf `F` on `X_étale` locally
computable from the sections of its direct image. An object `U` of `X_étale` is covered by
objects `Z` that are open and closed in a base change `X ×_Y V`, with open and closed complement
`Z'`; the sheaf condition for the two-element covering `{Z, Z'}` of `X ×_Y V` then extends any
section over `Z` to a section over `X ×_Y V` by taking the zero section on `Z'`, and sections over
`X ×_Y V` are exactly the sections of the direct image over `V`. Local surjectivity of the direct
image of a map of abelian sheaves therefore propagates back to local surjectivity of the map
itself, because base change carries covering sieves to covering sieves.

The remaining three assertions are formal consequences of the first, and are supplied by the
abstract results on a morphism of topoi.

## Main definitions

* `Stacks.EtaleCohomology.smallEtalePushforwardAb` — direct image of abelian sheaves on small
  étale sites.
* `Stacks.EtaleCohomology.smallEtaleAdjunctionAb` — the inverse-image/direct-image adjunction on
  abelian sheaves on small étale sites.

## Main results

* `Stacks.EtaleCohomology.smallEtalePushforwardAb_properties_of_hasPropertyA` — for a morphism
  with property (A), direct image reflects injections and surjections, the counit of the
  adjunction is surjective, and direct image is faithful.

## Implementation notes

Abelian sheaves are sheaves valued in `Ab`, and injections and surjections of abelian sheaves are
the monomorphisms and the epimorphisms. Surjectivity of a map of abelian sheaves on the small
étale site is equivalent to local surjectivity, which is what the geometric input is phrased in.

A disjoint union decomposition of `X ×_Y V` is recorded, as in `HasPropertyA`, by an isomorphism
from the binary coproduct of the two pieces, and the sheaf condition is applied to the covering
family indexed by `Bool` that the two pieces form.

## References

* [Stacks Project, Tag 04DK](https://stacks.math.columbia.edu/tag/04DK)
* [Stacks Project, Tag 04DA](https://stacks.math.columbia.edu/tag/04DA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-- Direct image of abelian sheaves along the morphism of small étale sites induced by
`f : X ⟶ Y`: it is restriction along the base-change functor `smallEtaleBaseChange f`, which is
continuous. -/
public def smallEtalePushforwardAb {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Sheaf (smallEtaleTopology X) Ab.{u + 1} ⥤ Sheaf (smallEtaleTopology Y) Ab.{u + 1} :=
  (smallEtaleBaseChange f).sheafPushforwardContinuous Ab.{u + 1}
    (smallEtaleTopology Y) (smallEtaleTopology X)

/-- The inverse-image/direct-image adjunction for abelian sheaves on the small étale sites of
`X` and `Y`, induced by a morphism `f : X ⟶ Y`. -/
public def smallEtaleAdjunctionAb {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (smallEtaleBaseChange f).sheafPullback Ab.{u + 1}
        (smallEtaleTopology Y) (smallEtaleTopology X) ⊣ smallEtalePushforwardAb f :=
  Functor.sheafAdjunctionContinuous (smallEtaleBaseChange f) Ab.{u + 1}
    (smallEtaleTopology Y) (smallEtaleTopology X)

/-- Property (A), recast as a covering of an object `U` of the small étale site of `X` by objects
`Z i` which sit as one half of a disjoint union decomposition `Z i ⨿ Z' i ≅ X ×_Y V i` of the base
change of an object `V i` of the small étale site of `Y`. -/
private lemma exists_clopen_cover_of_hasPropertyA {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : HasPropertyA f) (U : X.Etale) :
    ∃ (I : Type u) (Z : I → X.Etale) (p : ∀ i, Z i ⟶ U) (V : I → Y.Etale)
      (b : ∀ i, Z i ⟶ (smallEtaleBaseChange f).obj (V i)) (Z' : I → X.Etale)
      (b' : ∀ i, Z' i ⟶ (smallEtaleBaseChange f).obj (V i)),
      Sieve.ofArrows Z p ∈ smallEtaleTopology X U ∧
        ∀ i, ∃ e : (Z i).left ⨿ (Z' i).left ≅
            ((smallEtaleBaseChange f).obj (V i)).left,
          e.hom = coprod.desc (b i).left (b' i).left := by
  choose V g hg W W' e h hbase w hw using
    fun (x : U.left) => by
      have : Etale U.hom := U.prop
      exact hf U.hom x
  let Z (x : U.left) : X.Etale :=
    MorphismProperty.Over.mk (P := @Etale) (Q := ⊤) (h x ≫ U.hom) (by
      rw [hbase x]
      infer_instance)
  let p (x : U.left) : Z x ⟶ U := MorphismProperty.Over.homMk (h x)
  let V' (x : U.left) : Y.Etale :=
    MorphismProperty.Over.mk (P := @Etale) (Q := ⊤) (g x) (hg x)
  let Z' (x : U.left) : X.Etale :=
    MorphismProperty.Over.mk (P := @Etale) (Q := ⊤)
      (coprod.inr ≫ (e x).hom ≫ pullback.fst f (g x)) (by infer_instance)
  let b (x : U.left) : Z x ⟶ (smallEtaleBaseChange f).obj (V' x) :=
    MorphismProperty.Over.homMk
      (coprod.inl (X := W x) (Y := W' x) ≫ (e x).hom ≫ (pullbackSymmetry f (g x)).hom)
      (by
        show (coprod.inl (X := W x) (Y := W' x) ≫ (e x).hom ≫
          (pullbackSymmetry f (g x)).hom) ≫ pullback.snd (g x) f = h x ≫ U.hom
        rw [← Category.assoc, Category.assoc, pullbackSymmetry_hom_comp_snd]
        exact (hbase x).symm)
  let b' (x : U.left) : Z' x ⟶ (smallEtaleBaseChange f).obj (V' x) :=
    MorphismProperty.Over.homMk
      (coprod.inr ≫ (e x).hom ≫ (pullbackSymmetry f (g x)).hom)
      (by
        show (coprod.inr ≫ (e x).hom ≫ (pullbackSymmetry f (g x)).hom) ≫
          pullback.snd (g x) f = coprod.inr ≫ (e x).hom ≫ pullback.fst f (g x)
        rw [← Category.assoc, Category.assoc, pullbackSymmetry_hom_comp_snd]
        rfl)
  refine ⟨Σ x : U.left, (Z x).left, fun i ↦ Z i.1, fun i ↦ p i.1, fun i ↦ V' i.1,
    fun i ↦ b i.1, fun i ↦ Z' i.1, fun i ↦ b' i.1, ?_, ?_⟩
  · apply (Scheme.ofArrows_mem_smallEtaleTopology_iff (fun i : Σ x : U.left, (Z x).left ↦
      p i.1)).2
    ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    exact ⟨⟨x, w x⟩, w x, hw x⟩
  · intro i
    refine ⟨e i.1 ≪≫ pullbackSymmetry f (g i.1), ?_⟩
    ext
    · rw [coprod.inl_desc]
      rfl
    · rw [coprod.inr_desc]
      rfl

/-- The sheaf of sets underlying an abelian sheaf on the small étale site. -/
private def forgetSheaf {X : Scheme.{u}} (F : Sheaf (smallEtaleTopology X) Ab.{u + 1}) :
    Sheaf (smallEtaleTopology X) (Type (u + 1)) :=
  ⟨F.obj ⋙ CategoryTheory.forget Ab,
    (Presheaf.isSheaf_iff_isSheaf_forget (smallEtaleTopology X) F.obj
      (CategoryTheory.forget Ab)).mp F.property⟩

/-- Extension of a section across a two-element covering by subobjects with no common part: if
`a : A ⟶ P` and `b : B ⟶ P` cover `P`, are cancellable on the left, and no object with nonempty
underlying scheme maps into both over `P`, then every section over `A` is the restriction of a
section over `P`. -/
private lemma exists_section_of_clopen_pair {X : Scheme.{u}}
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1)))
    (A B P : X.Etale) (a : A ⟶ P) (b : B ⟶ P)
    (hcover : Sieve.ofArrows (Bool.rec A B) (Bool.rec a b) ∈ smallEtaleTopology X P)
    (hinjA : ∀ {W : X.Etale} (q r : W ⟶ A), q ≫ a = r ≫ a → q = r)
    (hinjB : ∀ {W : X.Etale} (q r : W ⟶ B), q ≫ b = r ≫ b → q = r)
    (hcross : ∀ {W : X.Etale} (q : W ⟶ A) (r : W ⟶ B), q ≫ a = r ≫ b → IsEmpty W.left)
    (s : F.obj.obj (Opposite.op A)) (tB : F.obj.obj (Opposite.op B)) :
    ∃ t : F.obj.obj (Opposite.op P), F.obj.map a.op t = s := by
  let Z : Bool → X.Etale := Bool.rec A B
  let m : ∀ i, Z i ⟶ P := Bool.rec a b
  let x : ∀ i, F.obj.obj (Opposite.op (Z i)) := Bool.rec s tB
  have hcompat : ∀ ⦃W : X.Etale⦄ ⦃i j : Bool⦄ (q : W ⟶ Z i) (r : W ⟶ Z j),
      q ≫ m i = r ≫ m j → F.obj.map q.op (x i) = F.obj.map r.op (x j) := by
    intro W i j q r hqr
    cases i <;> cases j
    · obtain rfl : q = r := hinjA q r (by simpa [Z, m] using hqr)
      rfl
    · have := subsingleton_sections_of_isEmpty F W (hcross q r (by simpa [Z, m] using hqr))
      exact Subsingleton.elim _ _
    · have := subsingleton_sections_of_isEmpty F W (hcross r q (by simpa [Z, m] using hqr.symm))
      exact Subsingleton.elim _ _
    · obtain rfl : q = r := hinjB q r (by simpa [Z, m] using hqr)
      rfl
  let xf : ∀ i, (PUnit.{u + 2} : Type (u + 1)) ⟶ F.obj.obj (Opposite.op (Z i)) :=
    fun i ↦ TypeCat.ofHom fun _ ↦ x i
  obtain ⟨t, ht⟩ := F.property.existsUnique_amalgamation_ofArrows m hcover xf
    fun W i j q r hqr ↦ by ext; simpa [xf] using hcompat q r hqr
  refine ⟨ConcreteCategory.hom t PUnit.unit, ?_⟩
  simpa [Z, m, x, xf] using ConcreteCategory.congr_hom (ht.1 false) PUnit.unit

/-- Extension of a section across a disjoint union decomposition: if `P` is the disjoint union of
`A` and `B` in the small étale site of `X`, then every section of an abelian sheaf over `A` is the
restriction of a section over `P`, namely of the one that is zero on `B`. -/
private lemma exists_section_of_coprod {X : Scheme.{u}}
    (F : Sheaf (smallEtaleTopology X) Ab.{u + 1})
    (A B P : X.Etale) (a : A ⟶ P) (b : B ⟶ P)
    (e : A.left ⨿ B.left ≅ P.left) (he : e.hom = coprod.desc a.left b.left)
    (s : ToType (F.obj.obj (Opposite.op A))) :
    ∃ t : ToType (F.obj.obj (Opposite.op P)), F.obj.map a.op t = s := by
  let Z : Bool → X.Etale := Bool.rec A B
  let m : ∀ i, Z i ⟶ P := Bool.rec a b
  have hA : a.left = coprod.inl ≫ e.hom := by rw [he, coprod.inl_desc]
  have hB : b.left = coprod.inr ≫ e.hom := by rw [he, coprod.inr_desc]
  have hcover : Sieve.ofArrows Z m ∈ smallEtaleTopology X P := by
    apply (Scheme.ofArrows_mem_smallEtaleTopology_iff m).2
    ext y
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    obtain ⟨q, hq⟩ := (ConcreteCategory.bijective_of_isIso e.hom.base).surjective y
    obtain ⟨q', hq'⟩ := (coprodMk A.left B.left).surjective q
    cases q' with
    | inl v =>
        refine ⟨false, v, ?_⟩
        show a.left v = y
        rw [← hq, ← hq']
        simp only [he, coprodMk_inl, ← Scheme.Hom.comp_apply, coprod.inl_desc]
    | inr v =>
        refine ⟨true, v, ?_⟩
        show b.left v = y
        rw [← hq, ← hq']
        simp only [he, coprodMk_inr, ← Scheme.Hom.comp_apply, coprod.inr_desc]
  have hinj : ∀ {C : X.Etale} (c : C ⟶ P) (ι : C.left ⟶ A.left ⨿ B.left) [Mono ι],
      c.left = ι ≫ e.hom → ∀ {W : X.Etale} (q r : W ⟶ C), q ≫ c = r ≫ c → q = r := by
    intro C c ι _ hc W q r hqr
    have : Mono c.left := by rw [hc]; infer_instance
    exact MorphismProperty.Over.Hom.ext
      ((cancel_mono c.left).1 (congrArg (fun k ↦ k.left) hqr))
  have hcross : ∀ {W : X.Etale} (q : W ⟶ A) (r : W ⟶ B), q ≫ a = r ≫ b → IsEmpty W.left := by
    intro W q r hqr
    have hqrL : q.left ≫ a.left = r.left ≫ b.left := congrArg (fun k ↦ k.left) hqr
    have h' : (q.left ≫ coprod.inl) ≫ e.hom = (r.left ≫ coprod.inr) ≫ e.hom := by
      simpa only [hA, hB, Category.assoc] using hqrL
    have h'' := (cancel_mono e.hom).1 h'
    refine ⟨fun v ↦ ?_⟩
    have hpt := congrArg (fun k : W.left ⟶ A.left ⨿ B.left ↦ k.base v) h''
    exact (AlgebraicGeometry.inl_ne_inr A.left B.left (q.left v) (r.left v)).elim hpt
  exact exists_section_of_clopen_pair (forgetSheaf F) A B P a b hcover
    (hinj a coprod.inl hA) (hinj b coprod.inr hB) hcross s
    (0 : ToType (F.obj.obj (Opposite.op B)))

/-- If the direct image of a map of abelian sheaves is locally surjective, then the map itself is
locally surjective over any base change `X ×_Y V`: a covering sieve of `V` in the small étale site
of `Y` is carried by base change, which is continuous, to a covering sieve of `X ×_Y V`. -/
private lemma imageSieve_baseChange_mem {X Y : Scheme.{u}} (f : X ⟶ Y)
    {F F' : Sheaf (smallEtaleTopology X) Ab.{u + 1}} (a : F ⟶ F')
    (ha : Presheaf.IsLocallySurjective (smallEtaleTopology Y)
      ((smallEtalePushforwardAb f).map a).hom)
    (V : Y.Etale) (t : F'.obj.obj (Opposite.op ((smallEtaleBaseChange f).obj V))) :
    Presheaf.imageSieve a.hom t ∈
      smallEtaleTopology X ((smallEtaleBaseChange f).obj V) := by
  have hS : Presheaf.imageSieve ((smallEtalePushforwardAb f).map a).hom t ∈
      smallEtaleTopology Y V := Presheaf.imageSieve_mem _ _ _
  have hcp := (CoverPreserving.of_isContinuous (smallEtaleBaseChange f)
    (smallEtaleTopology Y) (smallEtaleTopology X)).cover_preserve hS
  refine (smallEtaleTopology X).superset_covering ?_ hcp
  rw [Sieve.functorPushforward_le_iff_le_functorPullback]
  exact fun _ _ hk ↦ hk

/-- Direct image along a morphism with property (A) reflects local surjectivity of maps of
abelian sheaves. -/
private lemma isLocallySurjective_of_pushforward {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : HasPropertyA f) {F F' : Sheaf (smallEtaleTopology X) Ab.{u + 1}} (a : F ⟶ F')
    (ha : Presheaf.IsLocallySurjective (smallEtaleTopology Y)
      ((smallEtalePushforwardAb f).map a).hom) :
    Presheaf.IsLocallySurjective (smallEtaleTopology X) a.hom := by
  refine ⟨fun {U} s ↦ ?_⟩
  obtain ⟨I, Z, p, V, b, Z', b', hcover, hdecomp⟩ := exists_clopen_cover_of_hasPropertyA f hf U
  refine (smallEtaleTopology X).transitive hcover _ ?_
  intro W g hg
  rw [Presheaf.pullback_imageSieve]
  obtain ⟨i, k, hk⟩ := (Sieve.mem_ofArrows_iff Z p g).mp hg
  obtain ⟨e, he⟩ := hdecomp i
  obtain ⟨t, ht⟩ := exists_section_of_coprod F' (Z i) (Z' i)
    ((smallEtaleBaseChange f).obj (V i)) (b i) (b' i) e he (F'.obj.map (p i).op s)
  have h1 : Presheaf.imageSieve a.hom (F'.obj.map (p i).op s) ∈
      smallEtaleTopology X (Z i) := by
    rw [← ht, ← Presheaf.pullback_imageSieve]
    exact (smallEtaleTopology X).pullback_stable _ (imageSieve_baseChange_mem f a ha (V i) t)
  have h2 : F'.obj.map g.op s = F'.obj.map k.op (F'.obj.map (p i).op s) := by
    rw [hk, op_comp, F'.obj.map_comp, ConcreteCategory.comp_apply]
  rw [h2, ← Presheaf.pullback_imageSieve]
  exact (smallEtaleTopology X).pullback_stable _ h1

/-- **Stacks Project, Tag 04DK.** Let `f : X ⟶ Y` be a morphism of schemes with property (A).
Then direct image of abelian sheaves on the small étale sites reflects injections and
surjections, the counit `f^{-1} f_* F ⟶ F` is surjective for every abelian sheaf `F` on the
small étale site of `X`, and direct image is faithful. -/
@[stacks 04DK]
public theorem smallEtalePushforwardAb_properties_of_hasPropertyA {X Y : Scheme.{u}}
    (f : X ⟶ Y) (hf : HasPropertyA f) :
    (smallEtalePushforwardAb f).ReflectsMonomorphisms ∧
      (smallEtalePushforwardAb f).ReflectsEpimorphisms ∧
      (∀ F : Sheaf (smallEtaleTopology X) Ab.{u + 1},
          Epi ((smallEtaleAdjunctionAb f).counit.app F)) ∧
      (smallEtalePushforwardAb f).Faithful := by
  have hrefl : (smallEtalePushforwardAb f).ReflectsEpimorphisms := by
    refine ⟨fun {F F'} a ha ↦ ?_⟩
    have ha' : Presheaf.IsLocallySurjective (smallEtaleTopology Y)
        ((smallEtalePushforwardAb f).map a).hom :=
      (Sheaf.isLocallySurjective_iff_epi' _ ((smallEtalePushforwardAb f).map a)).2 ha
    have := isLocallySurjective_of_pushforward f hf a ha'
    exact Sheaf.epi_of_isLocallySurjective a
  have hcounit : ∀ F : Sheaf (smallEtaleTopology X) Ab.{u + 1},
      Epi ((smallEtaleAdjunctionAb f).counit.app F) :=
    (exactness_properties_bundled (smallEtaleAdjunctionAb f)).2.2.1 hrefl
  have hfaithful : (smallEtalePushforwardAb f).Faithful :=
    (exactness_properties_bundled (smallEtaleAdjunctionAb f)).2.1 hcounit
  exact ⟨Functor.reflectsMonomorphisms_of_faithful (smallEtalePushforwardAb f),
    hrefl, hcounit, hfaithful⟩

end Stacks.EtaleCohomology

end
