module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Subsheaf

/-!
# The local image of a morphism of abelian sheaves

Let `f : F ⟶ G` be a morphism of sheaves of abelian groups on a site `(C, J)`. Its *local image*
is the subsheaf of `G` whose sections over `U` are those `s` for which `f` hits `s` locally, that
is, for which the sieve of maps `V ⟶ U` pulling `s` back into the image of `f` is a covering
sieve. It is built here as a subfunctor of the underlying presheaf, shown to be a sheaf, and
compared with `F` and `G`.

## Main results

* `Stacks.Sites.LocalImage.epi_localSurjective`: an epimorphism of abelian sheaves is locally
  surjective. The local image of an epimorphism is the whole of `G`, so the comparison
  `F ⟶ localImageSheaf` exhibits `f` as locally surjective.

## Implementation notes

The conclusion `epi_localSurjective` reaches is also Mathlib's
`CategoryTheory.Sheaf.isLocallySurjective_iff_epi'`, but that lemma is not usable at this
generality: its only applicable instance constrains the carrier to `Type (max u v)`, so invoking
it would force `[J.WEqualsLocallyBijective AddCommGrpCat.{w}]` on every consumer. The
construction below needs only `[HasSheafify J AddCommGrpCat.{w}]` and leaves the section
universe `w` free, which is what the consumers are stated at.

Only `epi_localSurjective` is public; the thirteen declarations building the local image are
private, being plumbing for it.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite

universe w v u

namespace Stacks.Sites.LocalImage

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{w}]
  {F : Cᵒᵖ ⥤ AddCommGrpCat.{w}} {G : Sheaf J AddCommGrpCat.{w}} (f : F ⟶ G.obj)

private def localImageSubfunctor :
    Subfunctor (G.obj ⋙ forget AddCommGrpCat.{w}) :=
  (Subfunctor.range (whiskerRight f (forget AddCommGrpCat.{w}))).sheafify J

omit [HasSheafify J AddCommGrpCat.{w}] in
private theorem localImage_zero (U : Cᵒᵖ) :
    (0 : G.obj.obj U) ∈ (localImageSubfunctor J f).obj U := by
  change Presheaf.imageSieve f 0 ∈ J U.unop
  convert J.top_mem U.unop
  exact eq_top_iff.2 fun _ _ _ => ⟨0, by simp⟩

omit [HasSheafify J AddCommGrpCat.{w}] in
private theorem localImage_add (U : Cᵒᵖ) (s t : G.obj.obj U)
    (hs : s ∈ (localImageSubfunctor J f).obj U)
    (ht : t ∈ (localImageSubfunctor J f).obj U) :
    s + t ∈ (localImageSubfunctor J f).obj U := by
  change Presheaf.imageSieve f (s + t) ∈ J U.unop
  change Presheaf.imageSieve f s ∈ J U.unop at hs
  change Presheaf.imageSieve f t ∈ J U.unop at ht
  apply J.superset_covering _ (J.intersection_covering hs ht)
  rintro _ _ ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
  exact ⟨x + y, by simp only [_root_.map_add, hx, hy]⟩

omit [HasSheafify J AddCommGrpCat.{w}] in
private theorem localImage_neg (U : Cᵒᵖ) (s : G.obj.obj U)
    (hs : s ∈ (localImageSubfunctor J f).obj U) :
    -s ∈ (localImageSubfunctor J f).obj U := by
  change Presheaf.imageSieve f (-s) ∈ J U.unop
  change Presheaf.imageSieve f s ∈ J U.unop at hs
  apply J.superset_covering _ hs
  rintro _ _ ⟨x, hx⟩
  exact ⟨-x, by simp only [_root_.map_neg, hx]⟩

private def localImageSubgroup (U : Cᵒᵖ) : AddSubgroup (G.obj.obj U) where
  carrier := (localImageSubfunctor J f).obj U
  zero_mem' := localImage_zero J f U
  add_mem' := fun {s t} hs ht => localImage_add J f U s t hs ht
  neg_mem' := fun {s} hs => localImage_neg J f U s hs

private def localImagePresheaf : Cᵒᵖ ⥤ AddCommGrpCat.{w} where
  obj U := AddCommGrpCat.of (localImageSubgroup J f U)
  map {U V} i := AddCommGrpCat.ofHom {
    toFun := fun s => ⟨G.obj.map i s.val, (localImageSubfunctor J f).map i s.property⟩
    map_zero' := by ext; simp
    map_add' := by intros; ext; simp
  }
  map_id U := by
    ext s
    change G.obj.map (𝟙 U) s.val = s.val
    simp
  map_comp i j := by
    ext s
    change G.obj.map (i ≫ j) s.val = G.obj.map j (G.obj.map i s.val)
    simp

private def localImagePresheafι : localImagePresheaf J f ⟶ G.obj where
  app U := AddCommGrpCat.ofHom (localImageSubgroup J f U).subtype
  naturality U V i := by ext; rfl

omit [HasSheafify J AddCommGrpCat.{w}] in
private theorem localImagePresheaf_isSheaf :
    Presheaf.IsSheaf J (localImagePresheaf J f) := by
  apply Presheaf.isSheaf_of_isSheaf_comp J (s := forget AddCommGrpCat.{w})
  rw [isSheaf_iff_isSheaf_of_type]
  change Presieve.IsSheaf J (localImageSubfunctor J f).toFunctor
  apply Subfunctor.sheafify_isSheaf
  rw [← isSheaf_iff_isSheaf_of_type]
  exact GrothendieckTopology.HasSheafCompose.isSheaf G.obj G.2

private def localImageSheaf : Sheaf J AddCommGrpCat.{w} :=
  ⟨localImagePresheaf J f, localImagePresheaf_isSheaf J f⟩

private def localImageSheafι : localImageSheaf J f ⟶ G :=
  ⟨localImagePresheafι J f⟩

private def toLocalImageSheaf : F ⟶ (localImageSheaf J f).obj where
  app U := AddCommGrpCat.ofHom {
    toFun := fun s => ⟨f.app U s, by
      change Presheaf.imageSieve f (f.app U s) ∈ J U.unop
      rw [Presheaf.imageSieve_app]
      exact J.top_mem U.unop⟩
    map_zero' := by ext; simp
    map_add' := by intros; ext; simp
  }
  naturality U V i := by
    ext s
    exact Subtype.ext (f.naturality_apply i s)

omit [HasSheafify J AddCommGrpCat.{w}] in
private theorem toLocalImageSheaf_fac :
    toLocalImageSheaf J f ≫ (localImageSheafι J f).hom = f := by
  ext U s
  rfl

omit [HasSheafify J AddCommGrpCat.{w}] in
private theorem localImageSheafι_mono : Mono (localImageSheafι J f) := by
  apply (sheafToPresheaf J AddCommGrpCat.{w}).mono_of_mono_map
  change Mono (localImagePresheafι J f)
  have (U : Cᵒᵖ) : Mono ((localImagePresheafι J f).app U) :=
    (AddCommGrpCat.mono_iff_injective _).mpr Subtype.val_injective
  exact NatTrans.mono_of_mono_app _

omit [HasSheafify J AddCommGrpCat.{w}] in
private theorem isLocallySurjective_of_isIso [IsIso (localImageSheafι J f)] :
    Presheaf.IsLocallySurjective J f := by
  refine ⟨fun {U} s => ?_⟩
  obtain ⟨x, rfl⟩ := ((ConcreteCategory.isIso_iff_bijective
    ((localImageSheafι J f).hom.app (op U))).mp inferInstance).surjective s
  exact x.property

/-- If the inclusion of the local image of `f` is epic, then `f` is locally surjective. -/
private theorem isLocallySurjective_of_epi [Epi (localImageSheafι J f)] :
    Presheaf.IsLocallySurjective J f := by
  have := localImageSheafι_mono J f
  have := isIso_of_mono_of_epi (localImageSheafι J f)
  exact isLocallySurjective_of_isIso J f

variable {F G : Sheaf J AddCommGrpCat.{w}} (g : F ⟶ G)

/-- The sheaf-level comparison `F ⟶ localImageSheaf` of a morphism of sheaves with the local
image of its underlying map of presheaves. -/
private def toLocalImageSheafOfSheafHom : F ⟶ localImageSheaf J g.hom :=
  ⟨toLocalImageSheaf J g.hom⟩

omit [HasSheafify J AddCommGrpCat.{w}] in
private theorem toLocalImageSheafOfSheafHom_fac :
    toLocalImageSheafOfSheafHom J g ≫ localImageSheafι J g.hom = g :=
  Sheaf.hom_ext (toLocalImageSheaf_fac J g.hom)

/-- **An epimorphism of abelian sheaves is locally surjective.** The local image of `g` is a
subsheaf of `G` through which `g` factors, so an epimorphism makes its inclusion both monic and
epic, hence an isomorphism, and every section of `G` is then locally in the image. -/
public theorem epi_localSurjective [Epi g] : Sheaf.IsLocallySurjective g := by
  have := epi_of_epi_fac (toLocalImageSheafOfSheafHom_fac J g)
  exact isLocallySurjective_of_epi J g.hom

/-- **The unit of sheafification is locally surjective.** The local image of `toSheafify J P`
inside the sheafification of `P` receives a map back from the sheafification, by the adjunction
applied to the comparison `P ⟶ localImageSheaf`, so its monic inclusion is an isomorphism and
every section of the sheafification is locally a section of `P`.

Mathlib proves this for a carrier category satisfying `J.WEqualsLocallyBijective`, which
`AddCommGrpCat.{w}` is not known to satisfy at a free section universe `w`; this proof needs only
`[HasSheafify J AddCommGrpCat.{w}]`. -/
public theorem isLocallySurjective_toSheafify (P : Cᵒᵖ ⥤ AddCommGrpCat.{w}) :
    Presheaf.IsLocallySurjective J (toSheafify J P) := by
  let Q := (presheafToSheaf J AddCommGrpCat.{w}).obj P
  let u : P ⟶ Q.obj := toSheafify J P
  let ι : localImageSheaf J u ⟶ Q := localImageSheafι J u
  let q : Q ⟶ localImageSheaf J u :=
    ((sheafificationAdjunction J AddCommGrpCat.{w}).homEquiv P (localImageSheaf J u)).symm
      (toLocalImageSheaf J u)
  have hq : q ≫ ι = 𝟙 Q := by
    apply ((sheafificationAdjunction J AddCommGrpCat.{w}).homEquiv P Q).injective
    rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
    rfl
  have : Epi ι := epi_of_epi_fac hq
  exact isLocallySurjective_of_epi J u

end Stacks.Sites.LocalImage

end
