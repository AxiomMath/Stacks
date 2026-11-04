module

public import Mathlib.CategoryTheory.Sites.Subsheaf
public import Mathlib.Topology.Sheaves.CommRingCat

/-!
# Subsheaves of a sheaf of commutative rings, and images

Mathlib constructs the image of a morphism of *type*-valued sheaves as the sheafification of
the range subpresheaf (`CategoryTheory.Sheaf.image`), and deduces
`CategoryTheory.Limits.HasImages (CategoryTheory.Sheaf J (Type _))` from it.  This file carries
that construction across the forgetful functor to sheaves of **commutative rings**.

The point is that every subobject that occurs in the type-valued construction is a *subring* of
the ambient ring of sections: the range of a ring homomorphism is a subring, and — this is the
only non-formal step — the sheafification of a subring-valued subpresheaf is again
subring-valued, because two covering sieves have a covering intersection.

## Main definitions

* `Stacks.CategoryTheory.RingSubpresheaf`: a subring of the ring of sections over every object,
  stable under the restriction maps, together with the presheaf of commutative rings
  `Stacks.CategoryTheory.RingSubpresheaf.toPresheaf` it determines and its monomorphism
  `Stacks.CategoryTheory.RingSubpresheaf.ι` into the ambient presheaf.
* `Stacks.CategoryTheory.RingSubpresheaf.sheafify`: the sheafification of a subpresheaf of
  rings, again a subpresheaf of rings.
* `Stacks.CategoryTheory.RingSubpresheaf.range`: the range of a morphism of presheaves of
  commutative rings.
* `Stacks.CategoryTheory.Sheaf.ringImage`, `Stacks.CategoryTheory.Sheaf.toRingImage` and
  `Stacks.CategoryTheory.Sheaf.ringImageι`: the image of a morphism of sheaves of commutative
  rings, with its factorisation.

## Main results

* `Stacks.CategoryTheory.RingSubpresheaf.sheafify_isSheaf`: the sheafification of a subpresheaf
  of rings of a sheaf is a sheaf.
* `Stacks.CategoryTheory.RingSubpresheaf.sheafify_le`: it is the smallest subsheaf of rings
  containing the given subpresheaf.
* `Stacks.CategoryTheory.RingSubpresheaf.mem_sheafify_opens_iff`: on the site of the opens of a
  topological space, membership in the sheafification is membership locally.
* `Stacks.CategoryTheory.Sheaf.ringImageFactorisation` and the instance
  `CategoryTheory.Limits.HasImages (CategoryTheory.Sheaf J CommRingCat)`: sheaves of
  commutative rings have image factorisations.

## Implementation notes

`RingSubpresheaf` is a structure carrying a `Subring` for every object rather than a
`CategoryTheory.Subfunctor` of the underlying type-valued presheaf together with closure
properties, so that the ring of sections of `toPresheaf` is a `Subring` on the nose and the
restriction maps are `RingHom.restrict`.  The comparison with Mathlib's machinery is
`RingSubpresheaf.toSubfunctor`, whose sections over an object are the carrier of that subring,
and `RingSubpresheaf.forgetIso`, a natural isomorphism exhibiting the underlying type-valued
presheaf of `toPresheaf` as the one Mathlib builds.  Both are `Iso.refl`-level identifications;
they are stated as isomorphisms rather than equalities so that no functor-level `rfl` is ever
needed.

The universe restriction `CommRingCat.{max v u}` in the sheaf-theoretic part is forced by
`CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget`, which compares a sheaf of rings with a
sheaf of types in the same universe as the hom types of the site.  It is satisfied in the
intended application, where the site is the opens of a topological space in `Type u`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe w v u

namespace Stacks.CategoryTheory

/-- A *subpresheaf of rings* of a presheaf of commutative rings `F`: a subring of the ring of
sections of `F` over every object, stable under the restriction maps of `F`. -/
@[ext]
structure RingSubpresheaf {C : Type u} [Category.{v} C] (F : Cᵒᵖ ⥤ CommRingCat.{w}) where
  /-- The subring of sections over an object. -/
  obj (U : Cᵒᵖ) : Subring (F.obj U)
  /-- The subrings are stable under the restriction maps of `F`. -/
  map {U V : Cᵒᵖ} (i : U ⟶ V) (x : F.obj U) (hx : x ∈ obj U) : (F.map i).hom x ∈ obj V

namespace RingSubpresheaf

variable {C : Type u} [Category.{v} C] {F F' F'' : Cᵒᵖ ⥤ CommRingCat.{w}}

/-- Two subpresheaves of rings with the same subring over every object are equal. -/
theorem ext_obj {G G' : RingSubpresheaf F} (h : ∀ U, G.obj U = G'.obj U) : G = G' :=
  RingSubpresheaf.ext (funext h)

/-- Subpresheaves of rings are ordered by inclusion of the subrings over every object. -/
instance : PartialOrder (RingSubpresheaf F) :=
  PartialOrder.lift obj fun _ _ ↦ RingSubpresheaf.ext

/-- `G ≤ G'` exactly when `G.obj U ≤ G'.obj U` for every object `U`. -/
theorem le_def {G G' : RingSubpresheaf F} : G ≤ G' ↔ ∀ U, G.obj U ≤ G'.obj U := Iff.rfl

variable (G : RingSubpresheaf F)

/-- The subpresheaf of the underlying presheaf of types underlying a subpresheaf of rings. -/
@[simps obj]
def toSubfunctor : Subfunctor (F ⋙ forget CommRingCat) where
  obj U := (G.obj U : Set (F.obj U))
  map i x hx := G.map i x hx

/-- The underlying subpresheaves of types are ordered as the subpresheaves of rings are. -/
theorem toSubfunctor_le_iff {G G' : RingSubpresheaf F} :
    G.toSubfunctor ≤ G'.toSubfunctor ↔ G ≤ G' :=
  Iff.rfl

/-- The presheaf of commutative rings determined by a subpresheaf of rings. -/
@[simps obj]
def toPresheaf : Cᵒᵖ ⥤ CommRingCat.{w} where
  obj U := CommRingCat.of (G.obj U)
  map {U V} i :=
    CommRingCat.ofHom ((F.map i).hom.restrict (G.obj U) (G.obj V) fun x hx ↦ G.map i x hx)
  map_id U := by
    ext x
    change (F.map (𝟙 U)).hom x.val = x.val
    simp
  map_comp i j := by
    ext x
    change (F.map (i ≫ j)).hom x.val = (F.map j).hom ((F.map i).hom x.val)
    simp

/-- The inclusion of a subpresheaf of rings into the ambient presheaf. -/
@[simps app]
def ι : G.toPresheaf ⟶ F where
  app U := CommRingCat.ofHom (G.obj U).subtype
  naturality _ _ _ := by ext x; rfl

/-- The inclusion `G.ι` is injective on sections over every object. -/
theorem ι_app_injective (U : Cᵒᵖ) : Function.Injective (G.ι.app U).hom :=
  Subtype.val_injective

/-- The underlying presheaf of types of `G.toPresheaf` is the presheaf of types that Mathlib's
subpresheaf machinery attaches to `G.toSubfunctor`. -/
def forgetIso : G.toPresheaf ⋙ forget CommRingCat ≅ G.toSubfunctor.toFunctor :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun _ ↦ rfl

/-- The inclusion of a subpresheaf of rings into a larger one. -/
@[simps app]
def homOfLE {G G' : RingSubpresheaf F} (h : G ≤ G') : G.toPresheaf ⟶ G'.toPresheaf where
  app U := CommRingCat.ofHom (Subring.inclusion (h U))
  naturality _ _ _ := by ext x; rfl

/-- The inclusion `homOfLE h` composed with the inclusion of `G'` is the inclusion of `G`. -/
@[reassoc]
theorem homOfLE_ι {G G' : RingSubpresheaf F} (h : G ≤ G') : homOfLE h ≫ G'.ι = G.ι := by
  ext U x; rfl

section Lift

variable (f : F' ⟶ F) {G}

/-- A morphism of presheaves of commutative rings whose values lie in a subpresheaf of rings
factors through it. -/
@[simps app]
def lift (hf : ∀ (U : Cᵒᵖ) (x : F'.obj U), (f.app U).hom x ∈ G.obj U) : F' ⟶ G.toPresheaf where
  app U := CommRingCat.ofHom ((f.app U).hom.codRestrict (G.obj U) (hf U))
  naturality U V i := by
    ext x
    exact Subtype.ext (congrArg (fun g : F'.obj U ⟶ F.obj V ↦ g.hom x) (f.naturality i))

/-- The factorisation `lift f hf` composed with the inclusion `G.ι` is `f`. -/
@[reassoc]
theorem lift_ι (hf : ∀ (U : Cᵒᵖ) (x : F'.obj U), (f.app U).hom x ∈ G.obj U) :
    lift f hf ≫ G.ι = f := by
  ext U x
  rfl

end Lift

section Range

/-- The range of a morphism of presheaves of commutative rings, as a subpresheaf of rings of
the target. -/
@[simps obj]
def range (f : F' ⟶ F) : RingSubpresheaf F where
  obj U := (f.app U).hom.range
  map {U V} i x hx := by
    obtain ⟨y, rfl⟩ := RingHom.mem_range.mp hx
    exact RingHom.mem_range.mpr
      ⟨(F'.map i).hom y, congrArg (fun g : F'.obj U ⟶ F.obj V ↦ g.hom y) (f.naturality i)⟩

/-- The range of `f` lies in `G` exactly when every value of `f` on sections lies in `G`. -/
theorem range_le_iff {f : F' ⟶ F} {G : RingSubpresheaf F} :
    range f ≤ G ↔ ∀ (U : Cᵒᵖ) (x : F'.obj U), (f.app U).hom x ∈ G.obj U := by
  refine ⟨fun h U x ↦ h U (RingHom.mem_range_self _ x), fun h U x hx ↦ ?_⟩
  obtain ⟨y, rfl⟩ := RingHom.mem_range.mp hx
  exact h U y

/-- The range of `f ≫ g` is contained in the range of `g`. -/
theorem range_comp_le (f : F'' ⟶ F') (g : F' ⟶ F) : range (f ≫ g) ≤ range g :=
  range_le_iff.mpr fun U x ↦
    RingHom.mem_range.mpr ⟨(f.app U).hom x, rfl⟩

/-- The factorisation of a morphism of presheaves of commutative rings through its range. -/
def toRange (f : F' ⟶ F) : F' ⟶ (range f).toPresheaf :=
  lift f fun _ x ↦ RingHom.mem_range.mpr ⟨x, rfl⟩

/-- The factorisation `toRange f` composed with the inclusion of the range is `f`. -/
@[reassoc]
theorem toRange_ι (f : F' ⟶ F) : toRange f ≫ (range f).ι = f :=
  lift_ι f _

/-- A morphism of presheaves of commutative rings which is injective on sections is an
isomorphism onto its range. -/
theorem isIso_toRange (f : F' ⟶ F) (h : ∀ U, Function.Injective (f.app U).hom) :
    IsIso (toRange f) := by
  have : ∀ U, IsIso ((toRange f).app U) := fun U ↦ by
    rw [ConcreteCategory.isIso_iff_bijective]
    refine ⟨fun x y hxy ↦ h U (congrArg Subtype.val hxy), fun y ↦ ?_⟩
    obtain ⟨x, hx⟩ := RingHom.mem_range.mp y.2
    exact ⟨x, Subtype.ext hx⟩
  exact NatIso.isIso_of_isIso_app _

end Range

section Sheafify

variable (J : GrothendieckTopology C)

/-- The sheafification of a subpresheaf of rings: the sections which lie in it locally. Its
underlying subpresheaf of types is `CategoryTheory.Subfunctor.sheafify` of `G.toSubfunctor`. -/
def sheafify : RingSubpresheaf F where
  obj U :=
    { carrier := (G.toSubfunctor.sheafify J).obj U
      mul_mem' := by
        intro x y hx hy
        refine J.superset_covering ?_ (J.intersection_covering hx hy)
        rintro V g ⟨hg₁, hg₂⟩
        change (F.map g.op).hom (x * y) ∈ G.obj (op V)
        rw [map_mul]
        exact mul_mem hg₁ hg₂
      one_mem' := by
        refine J.superset_covering ?_ (J.top_mem _)
        intro V g _
        change (F.map g.op).hom 1 ∈ G.obj (op V)
        rw [map_one]
        exact one_mem _
      add_mem' := by
        intro x y hx hy
        refine J.superset_covering ?_ (J.intersection_covering hx hy)
        rintro V g ⟨hg₁, hg₂⟩
        change (F.map g.op).hom (x + y) ∈ G.obj (op V)
        rw [map_add]
        exact add_mem hg₁ hg₂
      zero_mem' := by
        refine J.superset_covering ?_ (J.top_mem _)
        intro V g _
        change (F.map g.op).hom 0 ∈ G.obj (op V)
        rw [map_zero]
        exact zero_mem _
      neg_mem' := by
        intro x hx
        refine J.superset_covering ?_ hx
        intro V g hg
        change (F.map g.op).hom (-x) ∈ G.obj (op V)
        rw [map_neg]
        exact neg_mem hg }
  map i _ hx := (G.toSubfunctor.sheafify J).map i hx

/-- The underlying subpresheaf of types of `G.sheafify J` is the sheafification of
`G.toSubfunctor`. -/
theorem toSubfunctor_sheafify : (G.sheafify J).toSubfunctor = G.toSubfunctor.sheafify J := rfl

/-- A section lies in `G.sheafify J` exactly when the sieve on which it restricts into `G` is
covering. -/
theorem mem_sheafify_iff {U : Cᵒᵖ} {x : F.obj U} :
    x ∈ (G.sheafify J).obj U ↔ G.toSubfunctor.sieveOfSection x ∈ J (unop U) :=
  Iff.rfl

/-- A subpresheaf of rings is contained in its sheafification. -/
theorem le_sheafify : G ≤ G.sheafify J :=
  G.toSubfunctor.le_sheafify J

variable {G J}

/-- If `F` is a sheaf, the sheafification of `G` is contained in every subpresheaf of rings
containing `G` whose underlying presheaf of types is a sheaf. -/
theorem sheafify_le {G G' : RingSubpresheaf F} (h : G ≤ G')
    (hF : Presieve.IsSheaf J (F ⋙ forget CommRingCat))
    (hG' : Presieve.IsSheaf J G'.toSubfunctor.toFunctor) : G.sheafify J ≤ G' :=
  Subfunctor.sheafify_le (G := G.toSubfunctor) (G' := G'.toSubfunctor) h hF hG'

/-- If `F` is a sheaf, the underlying presheaf of types of `G.sheafify J` is a sheaf. -/
theorem sheafify_isSheaf (hF : Presieve.IsSheaf J (F ⋙ forget CommRingCat)) :
    Presieve.IsSheaf J (G.sheafify J).toSubfunctor.toFunctor :=
  G.toSubfunctor.sheafify_isSheaf hF

end Sheafify

end RingSubpresheaf

/-! ### Sheaves of commutative rings

The remaining results compare the `CommRingCat`-valued sheaf condition with the type-valued one,
which forces the universe of the rings to be the one of the hom types of the site. -/

namespace RingSubpresheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {F F' : Cᵒᵖ ⥤ CommRingCat.{max v u}}

/-- A presheaf of commutative rings is a sheaf exactly when its underlying presheaf of types is
a sheaf. -/
theorem isSheaf_iff_isSheaf_forget (F : Cᵒᵖ ⥤ CommRingCat.{max v u}) :
    Presheaf.IsSheaf J F ↔ Presieve.IsSheaf J (F ⋙ forget CommRingCat) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget J F (forget CommRingCat),
    isSheaf_iff_isSheaf_of_type]

/-- `G.toPresheaf` is a sheaf exactly when the underlying presheaf of types of
`G.toSubfunctor` is a sheaf. -/
theorem isSheaf_toPresheaf_iff (G : RingSubpresheaf F) :
    Presheaf.IsSheaf J G.toPresheaf ↔ Presieve.IsSheaf J G.toSubfunctor.toFunctor :=
  (isSheaf_iff_isSheaf_forget J G.toPresheaf).trans
    ⟨Presieve.isSheaf_iso J G.forgetIso, Presieve.isSheaf_iso J G.forgetIso.symm⟩

/-- If `F` is a sheaf, the presheaf of rings determined by `G.sheafify J` is a sheaf. -/
theorem isSheaf_toPresheaf_sheafify (G : RingSubpresheaf F) (hF : Presheaf.IsSheaf J F) :
    Presheaf.IsSheaf J (G.sheafify J).toPresheaf :=
  (isSheaf_toPresheaf_iff J _).mpr (G.sheafify_isSheaf ((isSheaf_iff_isSheaf_forget J F).mp hF))

/-- The inclusion of a subpresheaf of rings is a monomorphism. -/
instance mono_ι (G : RingSubpresheaf F) : Mono G.ι :=
  (NatTrans.mono_iff_mono_app G.ι).mpr fun U ↦
    ConcreteCategory.mono_of_injective _ (G.ι_app_injective U)

end RingSubpresheaf

namespace Sheaf

open RingSubpresheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {F G : CategoryTheory.Sheaf J CommRingCat.{max v u}}

/-- The image of a morphism of sheaves of commutative rings: the sheafification of the
subpresheaf of rings given by its range. -/
def ringImage (f : F ⟶ G) : CategoryTheory.Sheaf J CommRingCat.{max v u} :=
  ⟨((range f.hom).sheafify J).toPresheaf, isSheaf_toPresheaf_sheafify J _ G.property⟩

/-- The inclusion of the image of a morphism of sheaves of commutative rings into its target. -/
def ringImageι (f : F ⟶ G) : ringImage f ⟶ G :=
  ObjectProperty.homMk ((range f.hom).sheafify J).ι

/-- The factorisation of a morphism of sheaves of commutative rings through its image. -/
def toRingImage (f : F ⟶ G) : F ⟶ ringImage f :=
  ObjectProperty.homMk (lift f.hom fun U x ↦
    le_sheafify _ J U (RingHom.mem_range.mpr ⟨x, rfl⟩))

/-- A morphism of sheaves of commutative rings factors as `toRingImage f ≫ ringImageι f`. -/
@[reassoc]
theorem toRingImage_ringImageι (f : F ⟶ G) : toRingImage f ≫ ringImageι f = f :=
  ObjectProperty.hom_ext _ (lift_ι _ _)

/-- The inclusion of the image of a morphism of sheaves of commutative rings is a
monomorphism. -/
instance mono_ringImageι (f : F ⟶ G) : Mono (ringImageι f) :=
  haveI : Mono (ringImageι f).hom := mono_ι _
  CategoryTheory.Sheaf.Hom.mono_of_presheaf_mono _ _ (ringImageι f)

section MonoFactorisation

variable {f : F ⟶ G}

/-- The middle object of any mono factorisation of `f` is isomorphic to the range of its
monomorphism, because a monomorphism of sheaves of commutative rings is injective on sections. -/
noncomputable def monoFactorisationRangeIso (I : Limits.MonoFactorisation f) :
    I.I.obj ≅ (range I.m.hom).toPresheaf :=
  have hm : Mono I.m.hom := (CategoryTheory.Sheaf.Hom.mono_iff_presheaf_mono J _ _).mp I.m_mono
  have hinj : ∀ U, Function.Injective (I.m.hom.app U).hom := fun U ↦ by
    have : Mono (I.m.hom.app U) := (NatTrans.mono_iff_mono_app I.m.hom).mp hm U
    exact ConcreteCategory.injective_of_mono_of_preservesPullback _
  haveI := isIso_toRange _ hinj
  asIso (toRange I.m.hom)

/-- The forward map of `monoFactorisationRangeIso I` is `toRange I.m.hom`. -/
theorem monoFactorisationRangeIso_hom (I : Limits.MonoFactorisation f) :
    (monoFactorisationRangeIso I).hom = toRange I.m.hom :=
  rfl

/-- The inverse of `monoFactorisationRangeIso I` composed with `I.m` is the inclusion of the
range of `I.m`. -/
@[reassoc]
theorem monoFactorisationRangeIso_inv_comp (I : Limits.MonoFactorisation f) :
    (monoFactorisationRangeIso I).inv ≫ I.m.hom = (range I.m.hom).ι := by
  rw [Iso.inv_comp_eq, monoFactorisationRangeIso_hom, toRange_ι]

/-- The range of the monomorphism of a mono factorisation of `f` contains the image of `f`. -/
theorem sheafify_range_le (I : Limits.MonoFactorisation f) :
    (range f.hom).sheafify J ≤ range I.m.hom := by
  have hsheaf : Presieve.IsSheaf J (range I.m.hom).toSubfunctor.toFunctor :=
    (isSheaf_toPresheaf_iff J _).mp
      ((Presheaf.isSheaf_of_iso_iff (monoFactorisationRangeIso I)).mp I.I.property)
  refine sheafify_le ?_ ((isSheaf_iff_isSheaf_forget J G.obj).mp G.property) hsheaf
  rw [range_le_iff]
  intro U x
  refine RingHom.mem_range.mpr ⟨(I.e.hom.app U).hom x, ?_⟩
  exact congrArg (fun g : F ⟶ G ↦ (g.hom.app U).hom x) I.fac

end MonoFactorisation

/-- The image of a morphism of sheaves of commutative rings is an image factorisation in the
categorical sense: it is the smallest subobject of the target through which the morphism
factors. -/
noncomputable def ringImageFactorisation (f : F ⟶ G) : Limits.ImageFactorisation f where
  F :=
    { I := ringImage f
      m := ringImageι f
      e := toRingImage f
      fac := toRingImage_ringImageι f }
  isImage :=
    { lift := fun I ↦ ObjectProperty.homMk
        (RingSubpresheaf.homOfLE (sheafify_range_le I) ≫ (monoFactorisationRangeIso I).inv)
      lift_fac := fun I ↦ ObjectProperty.hom_ext _ (by
        change (RingSubpresheaf.homOfLE (sheafify_range_le I) ≫
          (monoFactorisationRangeIso I).inv) ≫ I.m.hom = ((range f.hom).sheafify J).ι
        rw [Category.assoc, monoFactorisationRangeIso_inv_comp, homOfLE_ι]) }

/-- Sheaves of commutative rings have images. -/
instance hasImages : Limits.HasImages (CategoryTheory.Sheaf J CommRingCat.{max v u}) :=
  ⟨fun f ↦ ⟨⟨ringImageFactorisation f⟩⟩⟩

end Sheaf

namespace RingSubpresheaf

universe u'

/-- On the site of the opens of a topological space, a section lies in the sheafification of a
subpresheaf of rings exactly when every point of its domain has a neighbourhood on which it
restricts into the subpresheaf. -/
theorem mem_sheafify_opens_iff {T : Type u'} [TopologicalSpace T]
    {F : (Opens T)ᵒᵖ ⥤ CommRingCat.{w}} (G : RingSubpresheaf F) {U : Opens T}
    {x : F.obj (op U)} :
    x ∈ (G.sheafify (Opens.grothendieckTopology T)).obj (op U) ↔
      ∀ p ∈ U, ∃ (V : Opens T) (h : V ≤ U), p ∈ V ∧
        (F.map (CategoryTheory.homOfLE h).op).hom x ∈ G.obj (op V) := by
  rw [mem_sheafify_iff, Opens.mem_grothendieckTopology]
  refine ⟨fun h p hp ↦ ?_, fun h p hp ↦ ?_⟩
  · obtain ⟨V, f, hf, hpV⟩ := h p hp
    exact ⟨V, leOfHom f, hpV, hf⟩
  · obtain ⟨V, hVU, hpV, hx⟩ := h p hp
    exact ⟨V, CategoryTheory.homOfLE hVU, hx, hpV⟩

end RingSubpresheaf

end Stacks.CategoryTheory

namespace TopCat.Sheaf

universe u'

/-- Sheaves of commutative rings on a topological space have images. -/
instance hasImages (X : TopCat.{u'}) :
    CategoryTheory.Limits.HasImages (TopCat.Sheaf CommRingCat.{u'} X) :=
  inferInstanceAs
    (CategoryTheory.Limits.HasImages
      (CategoryTheory.Sheaf (Opens.grothendieckTopology X) CommRingCat.{u'}))

end TopCat.Sheaf

end

