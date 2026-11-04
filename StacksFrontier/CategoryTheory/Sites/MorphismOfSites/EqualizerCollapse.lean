module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Yoneda
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Whiskering
public import StacksFrontier.CategoryTheory.Sites.Continuous
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites.MorphismDefs
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SliceProduct
public import StacksFrontier.CategoryTheory.Sites.Stack.InheritedSite

/-!
# A morphism of sites that collapses an equalizer forces the empty cover

A continuous functor between sites need not define a morphism of sites: the left adjoint of its
pushforward on sheaves need not be left exact. This file isolates the obstruction in the form in
which a counterexample uses it.

Let `F : C ⥤ D` be a morphism of sites from `J` to `K` and let

```
E --e--> A --a,b--> B
```

be a fork exhibiting `e` as the equalizer of `a` and `b` in `C`. Left exactness of the left
adjoint `L` makes `L` carry that fork to a fork in sheaves on `D`; if `F.map a = F.map b` then
the second leg of the image fork is a pair of equal maps, so its equalizer leg is invertible.
Consequently the sheaf-theoretic size of `A` is bounded by that of `E`, and if `E` is covered by
the *empty* family for `J` then so is `F.obj A` for `K`. In the contrapositive — the shape a
counterexample needs — if `F.obj A` admits a morphism *to* nothing that could receive it, `F` was
not a morphism of sites after all.

The measurement of "sheaf-theoretic size" is done against the subobject classifier of the
topology, `CategoryTheory.Functor.closedSieves`, which is a sheaf
(`CategoryTheory.classifier_isSheaf`): a separated presheaf has at most one section over an
object covered by the empty family, so `Ω` is subsingleton at `F.obj A`, and the two closed
sieves `K.close ⊥` and `⊤` must agree.

This file also records two pieces of plumbing the same argument needs: the identification of the
topology a slice inherits along `CategoryTheory.Over.forget` with the localized topology, and a
criterion for continuity of a functor from continuity of its composite with a fully faithful
continuous and cocontinuous one. The second is how continuity of a functor into a full
subcategory of a site is read off from continuity into the ambient site.

## Main results

* `CategoryTheory.Over.forget_inheritedTopology`: `(Over.forget U).inheritedTopology J = J.over U`.
* `CategoryTheory.Functor.isContinuous_of_comp_of_fullyFaithful`: a functor whose composite with
  a fully faithful continuous and cocontinuous functor is continuous is continuous.
* `CategoryTheory.IsMorphismOfSites.bot_mem_of_equalizer_collapsed`: the empty family covers the
  image of the source of a collapsed equalizer.
* `CategoryTheory.GrothendieckTopology.bot_notMem_of_isEmpty_hom`: for a subcanonical topology,
  an object admitting no morphism to `Y` is not covered by the empty family.

## Implementation notes

`CategoryTheory.Over.forget_inheritedTopology` is proved at the level of precoverages first: the
inherited precoverage of `Over.forget U` is the comap of `J` along it, because the extra clause
of an inherited precoverage — that every member of a family be a strongly cartesian lift — is
automatic for `Over.forget U`, which is fibred in groupoids. The two generated topologies are
then compared with Mathlib's
`CategoryTheory.over_toGrothendieck_eq_toGrothendieck_comap_forget`.

In `bot_mem_of_equalizer_collapsed` the comparison between maps out of `L.obj (H.obj X)` and
sections of a sheaf at `F.obj X` is assembled from three adjunctions — the left adjoint of the
pushforward, sheafification, and the Yoneda equivalence — rather than from a single universal
property, so its naturality in `X` has to be checked by hand; `naturality` is that check, and it
is what turns `F.map a = F.map b` into `L.map (H.map a) = L.map (H.map b)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

universe v u

/-- **The topology a slice inherits along its forgetful functor is the localized topology.**

The inherited precoverage of `CategoryTheory.Over.forget U` is the comap of `J` along it: the
cartesianness clause of an inherited precoverage is automatic because `Over.forget U` is fibred
in groupoids, so every one of its morphisms is strongly cartesian. -/
theorem Over.forget_inheritedTopology {C : Type u} [Category.{v} C] [HasPullbacks C]
    (J : GrothendieckTopology C) (U : C) :
    (Over.forget U).inheritedTopology J = J.over U := by
  have hp : (Over.forget U).inheritedPrecoverage J.toPrecoverage =
      J.toPrecoverage.comap (Over.forget U) := by
    ext X R
    exact ⟨fun h => h.2, fun h => ⟨fun _ f _ =>
      (Functor.IsFiberedInGroupoids.over_forget U).isStronglyCartesian_homLift _ f, h⟩⟩
  rw [Functor.inheritedTopology_eq, hp,
    ← over_toGrothendieck_eq_toGrothendieck_comap_forget]
  congr 1
  refine le_antisymm J.toGrothendieck_toPrecoverage_le fun X R hR => ?_
  simpa using J.toPrecoverage.generate_mem_toGrothendieck
    (R := R.arrows) (by simpa [GrothendieckTopology.mem_toPrecoverage_iff] using hR)

/-- **Continuity of a functor into a site may be read off from continuity into a larger one.**

If `G : D ⥤ E` is fully faithful, continuous and cocontinuous, then the counit of the adjunction
it induces on sheaves is invertible, so a presheaf on `D` is a `K`-sheaf as soon as its
restriction along `F` of a `T`-sheaf pushed forward along `G` is; hence continuity of `F ⋙ G`
gives continuity of `F`. -/
theorem Functor.isContinuous_of_comp_of_fullyFaithful
    {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
    (F : C ⥤ D) (G : D ⥤ E)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (T : GrothendieckTopology E)
    [G.IsContinuous K T] [G.IsCocontinuous K T] [G.Full] [G.Faithful]
    [(F ⋙ G).IsContinuous J T] : F.IsContinuous J K := by
  refine ⟨fun Q => ?_⟩
  let adj := G.sheafAdjunctionCocontinuous (Type (max u v)) K T
  have : IsIso adj.counit :=
    Functor.isIso_sheafAdjunctionCocontinuous_counit G (Type (max u v)) K T
  exact (isSheaf_iff_isSheaf_of_type _ _).mp
    ((Presheaf.isSheaf_of_iso_iff (Functor.isoWhiskerLeft F.op
      ((sheafToPresheaf K _).mapIso (asIso (adj.counit.app Q))))).mp
      ((F ⋙ G).op_comp_isSheaf_of_isSheaf J T _
        ((G.sheafPushforwardCocontinuous (Type (max u v)) K T).obj Q).property))

/-- **The left adjoint of a pushforward identifies what `F` identifies.**

If `F` is continuous and `L` is left adjoint to the pushforward of sheaves along `F`, then two
maps `a b : A ⟶ B` with `F.map a = F.map b` have equal images under `L` after sheafified Yoneda:
maps out of `L` of the sheafified representable of `X` are sections of the pushforward at `X`,
naturally in `X`. -/
theorem Functor.map_uliftYoneda_sheafify_eq_of_map_eq
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D) [F.IsContinuous J K]
    {L : Sheaf J (Type (max u v)) ⥤ Sheaf K (Type (max u v))}
    (adj : L ⊣ F.sheafPushforwardContinuous (Type (max u v)) J K)
    {A B : C} {a b : A ⟶ B} (hab : F.map a = F.map b) :
    L.map ((uliftYoneda.{u} ⋙ presheafToSheaf J (Type (max u v))).map a) =
      L.map ((uliftYoneda.{u} ⋙ presheafToSheaf J (Type (max u v))).map b) := by
  let H := uliftYoneda.{u} ⋙ presheafToSheaf J (Type (max u v))
  -- The comparison is stated at the sections of the *pushforward* sheaf over `X`, which is the
  -- type the three adjunctions actually produce. That it agrees with the sections of `G` over
  -- `F.obj X` holds by definition but not at reducible transparency, so it is applied by hand
  -- through `hpush` below rather than left to unification.
  let push : Sheaf K (Type (max u v)) → Sheaf J (Type (max u v)) :=
    fun G => (F.sheafPushforwardContinuous (Type (max u v)) J K).obj G
  let equiv (X : C) (G : Sheaf K (Type (max u v))) :
      (L.obj (H.obj X) ⟶ G) ≃ (push G).obj.obj (op X) :=
    (adj.homEquiv _ _).trans
      (((sheafificationAdjunction J (Type (max u v))).homEquiv _ _).trans
        uliftYonedaEquiv)
  -- The naturality of `equiv` in `X` is the naturality of each of the three bijections it is
  -- built from, applied in turn. Each step is named with its type written out, so that the
  -- rewrites match at the spelling intended rather than up to an unfolding of `homEquiv`.
  have naturality {X Y : C} (f : X ⟶ Y) (G : Sheaf K (Type (max u v)))
      (k : L.obj (H.obj Y) ⟶ G) :
      equiv X G (L.map (H.map f) ≫ k) = (push G).obj.map f.op (equiv Y G k) := by
    have h₁ : adj.homEquiv (H.obj X) G (L.map (H.map f) ≫ k)
        = H.map f ≫ adj.homEquiv (H.obj Y) G k :=
      adj.homEquiv_naturality_left (H.map f) k
    have h₂ : (sheafificationAdjunction J (Type (max u v))).homEquiv
          (uliftYoneda.{u}.obj X) (push G) (H.map f ≫ adj.homEquiv (H.obj Y) G k)
        = uliftYoneda.{u}.map f ≫ (sheafificationAdjunction J (Type (max u v))).homEquiv
            (uliftYoneda.{u}.obj Y) (push G) (adj.homEquiv (H.obj Y) G k) :=
      (sheafificationAdjunction J (Type (max u v))).homEquiv_naturality_left
        (uliftYoneda.{u}.map f) (adj.homEquiv (H.obj Y) G k)
    have h₃ : (push G).obj.map f.op (uliftYonedaEquiv.{u}
          ((sheafificationAdjunction J (Type (max u v))).homEquiv
            (uliftYoneda.{u}.obj Y) (push G) (adj.homEquiv (H.obj Y) G k)))
        = uliftYonedaEquiv.{u} (uliftYoneda.{u}.map f ≫
            (sheafificationAdjunction J (Type (max u v))).homEquiv
              (uliftYoneda.{u}.obj Y) (push G) (adj.homEquiv (H.obj Y) G k)) :=
      uliftYonedaEquiv_naturality.{u} _ f.op
    show uliftYonedaEquiv.{u} ((sheafificationAdjunction J (Type (max u v))).homEquiv
        (uliftYoneda.{u}.obj X) (push G)
        (adj.homEquiv (H.obj X) G (L.map (H.map f) ≫ k))) = _
    rw [h₁, h₂]
    exact h₃.symm
  have hpush {X Y : C} (f : X ⟶ Y) (G : Sheaf K (Type (max u v))) :
      (push G).obj.map f.op = G.obj.map (F.map f).op := rfl
  apply (equiv A (L.obj (H.obj B))).injective
  have na := naturality a (L.obj (H.obj B)) (𝟙 _)
  have nb := naturality b (L.obj (H.obj B)) (𝟙 _)
  rw [Category.comp_id] at na nb
  rw [na, nb, hpush, hpush, hab]

/-- **A morphism of sites that collapses an equalizer forces the empty cover.**

Let `F` be a morphism of sites from `J` to `K`, let `e : E ⟶ A` be the equalizer of
`a b : A ⟶ B` in `C`, let the empty family cover `E` for `J`, and suppose `F.map a = F.map b`.
Then the empty family covers `F.obj A` for `K`.

The left adjoint `L` of the pushforward is left exact, so it carries the fork to a fork in
sheaves on `D`; the hypothesis `F.map a = F.map b` makes its second leg a pair of equal maps, so
the image of `e` is invertible. Testing against the subobject classifier of `K` — a sheaf, so
separated, so subsingleton at an object covered by the empty family — forces
`K.close ⊥ = ⊤`. -/
theorem IsMorphismOfSites.bot_mem_of_equalizer_collapsed
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [IsMorphismOfSites.{max u v} F J K]
    {A B E : C} (a b : A ⟶ B) (e : E ⟶ A) (he : e ≫ a = e ≫ b)
    (hl : IsLimit (Fork.ofι e he)) (hE : (⊥ : Sieve E) ∈ J E)
    (hab : F.map a = F.map b) : (⊥ : Sieve (F.obj A)) ∈ K (F.obj A) := by
  let H := uliftYoneda.{u} ⋙ presheafToSheaf J (Type (max u v))
  obtain ⟨L, ⟨adj⟩, hL⟩ := IsMorphismOfSites.hasExactLeftAdjoint (F := F) (J := J) (K := K)
  have : PreservesFiniteLimits L := hL
  let push : Sheaf K (Type (max u v)) → Sheaf J (Type (max u v)) :=
    fun G => (F.sheafPushforwardContinuous (Type (max u v)) J K).obj G
  let equiv (X : C) (G : Sheaf K (Type (max u v))) :
      (L.obj (H.obj X) ⟶ G) ≃ (push G).obj.obj (op X) :=
    (adj.homEquiv _ _).trans
      (((sheafificationAdjunction J (Type (max u v))).homEquiv _ _).trans
        uliftYonedaEquiv)
  have : IsIso (L.map (H.map e)) :=
    isIso_limit_cone_parallelPair_of_eq (F.map_uliftYoneda_sheafify_eq_of_map_eq J K adj hab)
      (isLimitForkMapOfIsLimit (H ⋙ L) he hl)
  let Ω : Sheaf K (Type (max u v)) :=
    ⟨(Functor.closedSieves K).toFunctor,
      (isSheaf_iff_isSheaf_of_type _ _).mpr (classifier_isSheaf K)⟩
  have hsub : Subsingleton ((push Ω).obj.obj (op A)) := by
    refine ⟨fun x y => ?_⟩
    apply (equiv A Ω).symm.injective
    apply (cancel_epi (L.map (H.map e))).mp
    apply (equiv E Ω).injective
    exact (((isSheaf_iff_isSheaf_of_type J (push Ω).obj).mp (push Ω).property).isSeparated
      _ hE).ext fun _ _ hf => False.elim hf
  change Subsingleton {T : Sieve (F.obj A) // K.IsClosed T} at hsub
  exact (K.close_eq_top_iff_mem _).mp (congrArg Subtype.val
    (hsub.elim ⟨_, K.close_isClosed ⊥⟩ ⟨⊤, fun _ _ _ => trivial⟩))

/-- **For a subcanonical topology, an object with no morphism to `Y` is not covered by the empty
family.** The representable presheaf of `Y` is a sheaf, and the empty family is a cover, so the
empty compatible family glues to a section over the object — that is, to a morphism to `Y`. -/
theorem GrothendieckTopology.bot_notMem_of_isEmpty_hom
    {C : Type*} [Category C] (J : GrothendieckTopology C) [J.Subcanonical]
    (X Y : C) (h : IsEmpty (X ⟶ Y)) : (⊥ : Sieve X) ∉ J X := by
  intro hc
  obtain ⟨f, -⟩ := GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (J := J)
    (_root_.CategoryTheory.yoneda.obj Y) (⊥ : Sieve X) hc (fun _ _ hg => False.elim hg)
    fun _ _ _ _ _ _ _ ha => False.elim ha
  exact h.false f

end CategoryTheory

end
