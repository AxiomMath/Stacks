module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.StalkAffineNhdsLimit.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.DiagonalComplementQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationClosedFibreGlueing
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationColimitOfLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationSize
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedPushforward

/-!
# Glueing algebraic spaces of finite presentation at a closed point (Stacks 0E90)

Let `S` be a scheme of a big fppf site and let `s ∈ S` be a closed point whose open complement
`U = S ∖ {s}` has quasi-compact inclusion. With `V = Spec 𝒪_{S,s} ∖ {s}` the punctured local
scheme, the comparison functor
`FP_S ⥤ FP_U ×_{FP_V} FP_{Spec 𝒪_{S,s}}`
is an equivalence of categories, where `FP_T` is the category of algebraic spaces of finite
presentation over `T`.

The objects `U`, `Spec 𝒪_{S,s}` and `V` are realised here as objects of the big fppf site of `S`:
the open subscheme `U`, the spectrum of the local ring with its canonical morphism
`Spec 𝒪_{S,s} ⟶ S`, and the open complement of the closed point of `Spec 𝒪_{S,s}`. All three
are subterminal objects of the site, since their structure morphisms to `S` are monomorphisms;
so every diagram of morphisms between them commutes. The comparison functor is the one attached
to the cartesian square with vertices `V`, `U`, `Spec 𝒪_{S,s}` and `S`.

The proof is the one of Stacks 0E90. The affine open neighbourhoods of `s` form a cofiltered
system with `Spec 𝒪_{S,s}` as its limit (`AlgebraicGeometry.isLimitSpecStalkCone`), and their
intersections with `U` form one with `V` as its limit, since every object involved is subterminal
in the site and `V` is the fibre product of `U` and `Spec 𝒪_{S,s}` over `S`; the intersections
are quasi-compact because `U ⟶ S` is. The index category has fewer objects than the cutoff of the
site, but in general not fewer than its cofinality, so the cofinality-free form of Stacks 07SK,
`AlgebraicGeometry.FinitePresentationSpacesOver.isFinitePresentationColimit_of_isLimit`, is used:
it turns the two limits into the two colimit statements that
`AlgebraicGeometry.FinitePresentationSpacesOver.isEquivalence_glueingFunctor_of_colimit`
combines with Stacks 0E8Z at each neighbourhood.

## Main definitions

* `AlgebraicGeometry.FinitePresentationSpacesOver.opensObj`: an open subscheme of `S` as an object
  of the big fppf site of `S`.
* `AlgebraicGeometry.FinitePresentationSpacesOver.localObj`: `Spec 𝒪_{S,s}` as an object of the
  big fppf site of `S`.
* `AlgebraicGeometry.FinitePresentationSpacesOver.puncturedOpens` and
  `AlgebraicGeometry.FinitePresentationSpacesOver.puncturedObj`: the punctured local scheme
  `Spec 𝒪_{S,s} ∖ {s}`, as an open of `Spec 𝒪_{S,s}` and as an object of the site.

## Main results

* `AlgebraicGeometry.FinitePresentationSpacesOver.isSubterminal_of_mono`: an object of the site
  whose structure morphism is a monomorphism of schemes is subterminal.
* `AlgebraicGeometry.FinitePresentationSpacesOver.isPullback_punctured`: the punctured local
  scheme is the base change of `U` to `Spec 𝒪_{S,s}` when `U` is the complement of a set of closed
  points containing `s`.
* `AlgebraicGeometry.FinitePresentationSpacesOver.isEquivalence_glueingFunctor_closedPoint`:
  **Stacks 0E90.**

## References

* [Stacks Project, Tag 0E90](https://stacks.math.columbia.edu/tag/0E90)
* [Stacks Project, Tag 0E8Z](https://stacks.math.columbia.edu/tag/0E8Z)
* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
* [Stacks Project, Tag 01YX](https://stacks.math.columbia.edu/tag/01YX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.FinitePresentationSpacesOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Subterminal objects of the site -/

/-- **An object of the big fppf site of `S` whose structure morphism is a monomorphism of schemes
is subterminal**: two morphisms into it from a common source agree, since both are compatible
with the structure morphisms to `S`. -/
theorem isSubterminal_of_mono {X : BigFppfOver B S hS} (hX : Mono (B.inclusion.map X.hom)) :
    IsSubterminal X := by
  intro T f g
  have : Mono X.hom := B.inclusion.mono_of_mono_map hX
  exact Over.OverMorphism.ext ((cancel_mono X.hom).1 ((Over.w f).trans (Over.w g).symm))

/-- A morphism out of a subterminal object is a monomorphism. -/
theorem mono_of_isSubterminal {C : Type*} [Category C] {X Y : C} (hX : IsSubterminal X)
    (f : X ⟶ Y) : Mono f :=
  ⟨fun _ _ _ => hX _ _⟩

/-! ### Open subschemes -/

include hS in
/-- An open subscheme of `S` is contained in the big fppf site. -/
theorem contains_opens (V : S.Opens) : B.Contains V :=
  (Scheme.size_coe_opens_le S V).trans_lt hS

/-- **An open subscheme of `S` as an object of the big fppf site of `S`**, with its open
immersion as structure morphism. -/
noncomputable def opensObj (V : S.Opens) : BigFppfOver B S hS :=
  BigFppfOver.mk B S hS (contains_opens B S hS V) V.ι

/-- The underlying scheme of `opensObj V` is `V`. -/
@[simp]
theorem toScheme_obj_opensObj (V : S.Opens) :
    (BigFppfOver.toScheme B S hS).obj (opensObj B S hS V) = V :=
  rfl

/-- The structure morphism of `opensObj V` is the open immersion `V ⟶ S`. -/
theorem inclusion_map_opensObj_hom (V : S.Opens) :
    B.inclusion.map (opensObj B S hS V).hom = V.ι :=
  rfl

/-- An open subscheme of `S` is a subterminal object of the site. -/
theorem isSubterminal_opensObj (V : S.Opens) : IsSubterminal (opensObj B S hS V) :=
  isSubterminal_of_mono B S hS (X := opensObj B S hS V) (inferInstanceAs (Mono V.ι))

/-- A morphism of the site into an open subscheme, from an object whose structure morphism lands
in it. -/
noncomputable def toOpensObj {T : BigFppfOver B S hS} (V : S.Opens)
    (h : Set.range (B.inclusion.map T.hom) ⊆ (V : Set S)) : T ⟶ opensObj B S hS V :=
  BigFppfOver.homMk B S hS (contains_opens B S hS V) V.ι
    (IsOpenImmersion.lift V.ι (B.inclusion.map T.hom) (by simpa using h))
    (IsOpenImmersion.lift_fac _ _ _)

/-- The inclusion of open subschemes `V ⊆ V'` of `S`, in the site. -/
noncomputable def opensHomOfLE {V V' : S.Opens} (h : V ≤ V') :
    opensObj B S hS V ⟶ opensObj B S hS V' :=
  BigFppfOver.homMk B S hS (contains_opens B S hS V') V'.ι (T := opensObj B S hS V) (S.homOfLE h)
    (Scheme.homOfLE_ι _ _)

/-- The underlying morphism of schemes of `opensHomOfLE h` is the inclusion `V ⟶ V'`. -/
@[simp]
theorem toScheme_map_opensHomOfLE {V V' : S.Opens} (h : V ≤ V') :
    (BigFppfOver.toScheme B S hS).map (opensHomOfLE B S hS h) = S.homOfLE h :=
  rfl

/-- The underlying morphism of schemes of `toOpensObj V h` is the lift through the open
immersion `V ⟶ S`. -/
@[simp]
theorem toScheme_map_toOpensObj {T : BigFppfOver B S hS} (V : S.Opens)
    (h : Set.range (B.inclusion.map T.hom) ⊆ (V : Set S)) :
    (BigFppfOver.toScheme B S hS).map (toOpensObj B S hS V h) =
      IsOpenImmersion.lift V.ι (B.inclusion.map T.hom) (by simpa using h) :=
  rfl

/-! ### The local scheme and its puncture -/

include hS in
/-- `Spec 𝒪_{S,s}` is contained in the big fppf site: the canonical morphism to `S` is a
monomorphism. -/
theorem contains_local (s : S) : B.Contains (Spec (S.presheaf.stalk s)) :=
  B.contains_of_mono (S.fromSpecStalk s) hS

/-- **`Spec 𝒪_{S,s}` as an object of the big fppf site of `S`**, with the canonical morphism
`Spec 𝒪_{S,s} ⟶ S` as structure morphism. -/
noncomputable def localObj (s : S) : BigFppfOver B S hS :=
  BigFppfOver.mk B S hS (contains_local B S hS s) (S.fromSpecStalk s)

/-- The structure morphism of `localObj s` is the canonical morphism `Spec 𝒪_{S,s} ⟶ S`. -/
theorem inclusion_map_localObj_hom (s : S) :
    B.inclusion.map (localObj B S hS s).hom = S.fromSpecStalk s :=
  rfl

/-- `Spec 𝒪_{S,s}` is a subterminal object of the site. -/
theorem isSubterminal_localObj (s : S) : IsSubterminal (localObj B S hS s) :=
  isSubterminal_of_mono B S hS (X := localObj B S hS s)
    (by rw [inclusion_map_localObj_hom]; exact inferInstanceAs (Mono (S.fromSpecStalk s)))

/-- The punctured local scheme `Spec 𝒪_{S,s} ∖ {s}`, as the open complement of the closed point
of `Spec 𝒪_{S,s}`. -/
def puncturedOpens (s : S) : (Spec (S.presheaf.stalk s)).Opens :=
  ⟨{IsLocalRing.closedPoint (S.presheaf.stalk s)}ᶜ,
    (IsLocalRing.isClosed_singleton_closedPoint _).isOpen_compl⟩

include hS in
/-- The punctured local scheme `Spec 𝒪_{S,s} ∖ {s}` is contained in the big fppf site. -/
theorem contains_punctured (s : S) : B.Contains (puncturedOpens S s) :=
  (Scheme.size_coe_opens_le _ _).trans_lt (contains_local B S hS s)

/-- **The punctured local scheme `Spec 𝒪_{S,s} ∖ {s}` as an object of the big fppf site of
`S`**, with structure morphism the composite of its open immersion into `Spec 𝒪_{S,s}` and the
canonical morphism to `S`. -/
noncomputable def puncturedObj (s : S) : BigFppfOver B S hS :=
  BigFppfOver.mk B S hS (contains_punctured B S hS s) ((puncturedOpens S s).ι ≫ S.fromSpecStalk s)

/-- The structure morphism of `puncturedObj s` is the open immersion into `Spec 𝒪_{S,s}`
followed by the canonical morphism to `S`. -/
theorem inclusion_map_puncturedObj_hom (s : S) :
    B.inclusion.map (puncturedObj B S hS s).hom = (puncturedOpens S s).ι ≫ S.fromSpecStalk s :=
  rfl

/-- The punctured local scheme is a subterminal object of the site. -/
theorem isSubterminal_puncturedObj (s : S) : IsSubterminal (puncturedObj B S hS s) :=
  isSubterminal_of_mono B S hS (X := puncturedObj B S hS s) (by
    rw [inclusion_map_puncturedObj_hom]
    exact inferInstanceAs (Mono ((puncturedOpens S s).ι ≫ S.fromSpecStalk s)))

/-- The open immersion of the punctured local scheme into the local scheme, in the site. -/
noncomputable def puncturedToLocal (s : S) : puncturedObj B S hS s ⟶ localObj B S hS s :=
  BigFppfOver.homMk B S hS (contains_local B S hS s) (S.fromSpecStalk s)
    (T := puncturedObj B S hS s) (puncturedOpens S s).ι rfl

/-- **The canonical morphism `Spec 𝒪_{S,s} ⟶ S` is injective on points.** -/
theorem fromSpecStalk_injective (s : S) : Function.Injective (S.fromSpecStalk s) :=
  (S.fromSpecStalk s).isEmbedding.injective

/-- **A point of the punctured local scheme maps into the complement of any set of closed points
containing `s`.** Its image is a generization of `s` other than `s`, and a closed point that
generizes `s` is `s` itself. -/
theorem fromSpecStalk_mem_of_ne_closedPoint {s : S} {F : Set S} (hF : ∀ x ∈ F, IsClosed {x})
    (y : Spec (S.presheaf.stalk s)) (hy : y ≠ IsLocalRing.closedPoint _) :
    S.fromSpecStalk s y ∉ F := by
  intro hyF
  have hsp : S.fromSpecStalk s y ⤳ s := by
    have := (IsLocalRing.specializes_closedPoint y).map (S.fromSpecStalk s).continuous
    rwa [Scheme.fromSpecStalk_closedPoint] at this
  have heq : S.fromSpecStalk s y = s :=
    (hsp.mem_closed (hF _ hyF) rfl).symm
  exact hy (fromSpecStalk_injective S s (heq.trans Scheme.fromSpecStalk_closedPoint.symm))

/-- **The preimage of the complement of a set of closed points containing `s` in `Spec 𝒪_{S,s}`
is the punctured local scheme.** -/
theorem preimage_eq_puncturedOpens {s : S} {F : Set S} (hF : ∀ x ∈ F, IsClosed {x})
    (hsF : s ∈ F) (U : S.Opens) (hU : (U : Set S) = Fᶜ) :
    S.fromSpecStalk s ⁻¹ᵁ U = puncturedOpens S s := by
  ext y
  show S.fromSpecStalk s y ∈ (U : Set S) ↔
    y ∉ ({IsLocalRing.closedPoint (S.presheaf.stalk s)} : Set (Spec (S.presheaf.stalk s)))
  rw [hU]
  constructor
  · intro h hy
    exact h (by rw [Set.mem_singleton_iff.1 hy, Scheme.fromSpecStalk_closedPoint]; exact hsF)
  · intro hy
    exact fromSpecStalk_mem_of_ne_closedPoint S hF y fun h => hy (Set.mem_singleton_iff.2 h)

/-! ### The cartesian squares -/

/-- The terminal object of the site is subterminal. -/
theorem isSubterminal_base : IsSubterminal (Over.mk (𝟙 (B.obj hS))) :=
  isSubterminal_of_isTerminal Over.mkIdTerminal

/-- **Pullbacks in the site are detected on underlying schemes**, for a square over a
subterminal object. -/
theorem isPullback_of_toScheme {P X Y Z : BigFppfOver B S hS} {fst : P ⟶ X} {snd : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (hZ : IsSubterminal Z)
    (h : IsPullback ((BigFppfOver.toScheme B S hS).map fst)
      ((BigFppfOver.toScheme B S hS).map snd) ((BigFppfOver.toScheme B S hS).map f)
      ((BigFppfOver.toScheme B S hS).map g)) :
    IsPullback fst snd f g :=
  IsPullback.of_map (BigFppfOver.toScheme B S hS) (hZ _ _) h

/-- The intersection of two opens is their fibre product over `S`, in the site. -/
theorem isPullback_opensObj_inf (V V' : S.Opens) :
    IsPullback (opensHomOfLE B S hS (inf_le_left : V ⊓ V' ≤ V))
      (opensHomOfLE B S hS (inf_le_right : V ⊓ V' ≤ V'))
      (toBase B S hS (opensObj B S hS V)) (toBase B S hS (opensObj B S hS V')) := by
  apply isPullback_of_toScheme B S hS (isSubterminal_base B S hS)
  rw [toScheme_map_eq_inclusion_map_hom, toScheme_map_eq_inclusion_map_hom]
  exact isPullback_opens_inf V V'

variable {S} in
/-- The punctured local scheme lies over the complement of any set of closed points containing
`s`. -/
theorem range_puncturedObj_subset {s : S} {F : Set S} (hF : ∀ x ∈ F, IsClosed {x}) (hsF : s ∈ F)
    (U : S.Opens) (hU : (U : Set S) = Fᶜ) :
    Set.range (B.inclusion.map (puncturedObj B S hS s).hom) ⊆ (U : Set S) := by
  rintro _ ⟨y, rfl⟩
  have hy : (puncturedOpens S s).ι y ∈ S.fromSpecStalk s ⁻¹ᵁ U := by
    rw [preimage_eq_puncturedOpens S hF hsF U hU]
    have h := Set.mem_range_self (f := (puncturedOpens S s).ι) y
    rwa [Scheme.Opens.range_ι] at h
  exact hy

/-- The morphism from the punctured local scheme to the complement of a set of closed points
containing `s`. -/
noncomputable def puncturedToOpens {s : S} {F : Set S} (hF : ∀ x ∈ F, IsClosed {x})
    (hsF : s ∈ F) (U : S.Opens) (hU : (U : Set S) = Fᶜ) :
    puncturedObj B S hS s ⟶ opensObj B S hS U :=
  toOpensObj B S hS U (range_puncturedObj_subset B hS hF hsF U hU)

/-- **The punctured local scheme is the base change of the complement of a set of closed points
containing `s` to `Spec 𝒪_{S,s}`**, as a cartesian square of the site. -/
theorem isPullback_punctured {s : S} {F : Set S} (hF : ∀ x ∈ F, IsClosed {x}) (hsF : s ∈ F)
    (U : S.Opens) (hU : (U : Set S) = Fᶜ) :
    IsPullback (puncturedToOpens B S hS hF hsF U hU) (puncturedToLocal B S hS s)
      (toBase B S hS (opensObj B S hS U)) (toBase B S hS (localObj B S hS s)) := by
  apply isPullback_of_toScheme B S hS (isSubterminal_base B S hS)
  rw [toScheme_map_eq_inclusion_map_hom, toScheme_map_eq_inclusion_map_hom]
  refine IsOpenImmersion.isPullback _ (puncturedOpens S s).ι U.ι (S.fromSpecStalk s)
    (IsOpenImmersion.lift_fac _ _ _).symm ?_
  rw [Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι]
  exact preimage_eq_puncturedOpens S hF hsF U hU

/-! ### The systems of neighbourhoods -/

/-- **The affine open neighbourhoods of `s`, as a cofiltered system of objects of the site.** -/
noncomputable def nbhdSystem (s : S) : AffineOpenNhds S s ⥤ BigFppfOver B S hS where
  obj W := opensObj B S hS W.obj.1
  map f := opensHomOfLE B S hS (leOfHom ((affineOpenNhds S s).ι.map f))
  map_id _ := isSubterminal_opensObj B S hS _ _ _
  map_comp _ _ := isSubterminal_opensObj B S hS _ _ _

/-- **The intersections of the affine open neighbourhoods of `s` with an open `U`, as a
cofiltered system of objects of the site.** -/
noncomputable def nbhdInterSystem (s : S) (U : S.Opens) :
    AffineOpenNhds S s ⥤ BigFppfOver B S hS where
  obj W := opensObj B S hS (U ⊓ W.obj.1)
  map f := opensHomOfLE B S hS (inf_le_inf_left U (leOfHom ((affineOpenNhds S s).ι.map f)))
  map_id _ := isSubterminal_opensObj B S hS _ _ _
  map_comp _ _ := isSubterminal_opensObj B S hS _ _ _

variable {S} in
/-- The local scheme lies over every open neighbourhood of `s`. -/
theorem range_localObj_subset {s : S} (V : S.Opens) (hs : s ∈ V) :
    Set.range (B.inclusion.map (localObj B S hS s).hom) ⊆ (V : Set S) := by
  rintro _ ⟨y, rfl⟩
  have hy : S.fromSpecStalk s y ⤳ s := by
    have h := Set.mem_range_self (f := S.fromSpecStalk s) y
    rwa [Scheme.range_fromSpecStalk] at h
  exact hy.mem_open V.2 hs

/-- The legs of the cone of the local scheme over the neighbourhoods of `s`. -/
noncomputable def localToNbhd (s : S) (W : AffineOpenNhds S s) :
    localObj B S hS s ⟶ (nbhdSystem B S hS s).obj W :=
  toOpensObj B S hS W.obj.1 (range_localObj_subset B hS W.obj.1 W.obj.2)

/-- The legs of the cone of the punctured local scheme over the intersections of the
neighbourhoods of `s` with `U`. -/
noncomputable def puncturedToNbhdInter {s : S} {F : Set S} (hF : ∀ x ∈ F, IsClosed {x})
    (hsF : s ∈ F) (U : S.Opens) (hU : (U : Set S) = Fᶜ) (W : AffineOpenNhds S s) :
    puncturedObj B S hS s ⟶ (nbhdInterSystem B S hS s U).obj W :=
  toOpensObj B S hS (U ⊓ W.obj.1) (fun _ hx => ⟨range_puncturedObj_subset B hS hF hsF U hU hx,
    (range_localObj_subset B hS W.obj.1 W.obj.2 (by
      obtain ⟨y, rfl⟩ := hx
      exact ⟨(puncturedOpens S s).ι y, rfl⟩))⟩)

/-- The intersection of two opens over a third is their fibre product over it. -/
theorem isPullback_homOfLE {P X Y Z : S.Opens} (hPX : P ≤ X) (hPY : P ≤ Y) (hXZ : X ≤ Z)
    (hYZ : Y ≤ Z) (hP : P = X ⊓ Y) :
    IsPullback (S.homOfLE hPX) (S.homOfLE hPY) (S.homOfLE hXZ) (S.homOfLE hYZ) := by
  subst hP
  exact isPullback_opens_inf_le hXZ hYZ

/-- The Yoneda image of a morphism of the site whose underlying morphism of schemes is affine is
an affine morphism of algebraic spaces. -/
theorem isAffineHom_yoneda_map_of_isAffineHom {X Y : BigFppfOver B S hS} (φ : X ⟶ Y)
    (h : IsAffineHom ((BigFppfOver.toScheme B S hS).map φ)) :
    Space.IsAffineHom B S hS (yoneda.map φ) :=
  Space.isAffineHom_of_presheaf ((Space.presheaf_yoneda_map_iff B S hS
    (P := @AlgebraicGeometry.IsAffineHom.{u}) inferInstance φ).2 h)

/-! ### The two limits -/

/-- The legs of the cone of the local scheme are the canonical morphisms
`Spec 𝒪_{S,s} ⟶ W`. -/
theorem toScheme_map_localToNbhd (s : S) (W : AffineOpenNhds S s) :
    (BigFppfOver.toScheme B S hS).map (localToNbhd B S hS s W) =
      Scheme.Opens.fromSpecStalkOfMem W.obj.1 s W.obj.2 :=
  (IsOpenImmersion.lift_uniq (Scheme.Opens.ι (X := S) W.obj.1) (S.fromSpecStalk s) _
    (Scheme.Opens.fromSpecStalkOfMem W.obj.1 s W.obj.2)
    (Scheme.Opens.fromSpecStalkOfMem_ι _ _ _)).symm

/-- The cone of the local scheme over the affine open neighbourhoods of `s`. -/
noncomputable def localCone (s : S) : Cone (nbhdSystem B S hS s) where
  pt := localObj B S hS s
  π :=
    { app := localToNbhd B S hS s
      naturality := fun _ _ _ => isSubterminal_opensObj B S hS _ _ _ }

/-- **`Spec 𝒪_{S,s}` is the limit of the affine open neighbourhoods of `s`**, read in schemes:
this is `AlgebraicGeometry.isLimitSpecStalkCone`. -/
noncomputable def isLimitToSchemeLocalCone (s : S) :
    IsLimit ((BigFppfOver.toScheme B S hS).mapCone (localCone B S hS s)) := by
  refine (isLimitSpecStalkCone S s).ofIsoLimit (Cone.ext (Iso.refl _) fun W => ?_)
  exact ((Category.id_comp _).trans (toScheme_map_localToNbhd B S hS s W)).symm

/-- **`Spec 𝒪_{S,s}` is the limit of the affine open neighbourhoods of `s`**, in the site. -/
noncomputable def isLimitLocalCone (s : S) : IsLimit (localCone B S hS s) := by
  have : IsConnected (AffineOpenNhds S s) := IsCofiltered.isConnected _
  exact isLimitOfReflects (BigFppfOver.toScheme B S hS) (isLimitToSchemeLocalCone B S hS s)

/-- The cone of the punctured local scheme over the intersections of the neighbourhoods of `s`
with `U`. -/
noncomputable def puncturedCone {s : S} {F : Set S} (hF : ∀ x ∈ F, IsClosed {x})
    (hsF : s ∈ F) (U : S.Opens) (hU : (U : Set S) = Fᶜ) :
    Cone (nbhdInterSystem B S hS s U) where
  pt := puncturedObj B S hS s
  π :=
    { app := puncturedToNbhdInter B S hS hF hsF U hU
      naturality := fun _ _ _ => isSubterminal_opensObj B S hS _ _ _ }

/-- **The punctured local scheme is the limit of the intersections of the affine open
neighbourhoods of `s` with `U`**, in the site. Every object involved is subterminal, so a cone
over the intersections is a compatible family of morphisms to the neighbourhoods, which factors
through `Spec 𝒪_{S,s}`, together with a morphism to `U`; the punctured local scheme is the fibre
product of the two. -/
noncomputable def isLimitPuncturedCone {s : S} {F : Set S} (hF : ∀ x ∈ F, IsClosed {x})
    (hsF : s ∈ F) (U : S.Opens) (hU : (U : Set S) = Fᶜ) :
    IsLimit (puncturedCone B S hS hF hsF U hU) where
  lift c := (isPullback_punctured B S hS hF hsF U hU).lift
    (c.π.app (Classical.arbitrary _) ≫ opensHomOfLE B S hS inf_le_left)
    ((isLimitLocalCone B S hS s).lift
      { pt := c.pt
        π :=
          { app := fun W => c.π.app W ≫ opensHomOfLE B S hS inf_le_right
            naturality := fun _ _ _ => isSubterminal_opensObj B S hS _ _ _ } })
    (isSubterminal_base B S hS _ _)
  fac _ _ := isSubterminal_opensObj B S hS _ _ _
  uniq _ _ _ := isSubterminal_puncturedObj B S hS _ _ _

/-! ### The hypotheses of Stacks 07SK for the two systems -/

include hS in
/-- There are fewer affine open neighbourhoods of `s` than the cutoff of the site. -/
theorem mk_affineOpenNhds_lt (s : S) : Cardinal.mk (AffineOpenNhds S s) < B.cutoff := by
  refine (Cardinal.mk_le_of_injective (f := fun W : AffineOpenNhds S s =>
    (⟨W.obj.1, W.property⟩ : S.affineOpens)) fun W W' h => ?_).trans_lt
    (S.mk_affineOpens_le_size.trans_lt hS)
  obtain ⟨⟨V, hV⟩, hA⟩ := W
  obtain ⟨⟨V', hV'⟩, hA'⟩ := W'
  have : V = V' := congrArg Subtype.val h
  subst this
  rfl

/-- Between two affine open neighbourhoods of `s` there is at most one morphism. -/
theorem mk_hom_affineOpenNhds_le (s : S) (W W' : AffineOpenNhds S s) :
    Cardinal.mk (W ⟶ W') ≤ 1 :=
  Cardinal.le_one_iff_subsingleton.2
    ⟨fun _ _ => (affineOpenNhds S s).ι.map_injective (Subsingleton.elim _ _)⟩

/-- The transition morphisms of the system of affine open neighbourhoods of `s` are affine. -/
theorem isAffineHom_nbhdSystem (s : S) {W W' : AffineOpenNhds S s} (f : W ⟶ W') :
    Space.IsAffineHom B S hS ((nbhdSystem B S hS s ⋙ yoneda).map f) :=
  isAffineHom_yoneda_map_of_isAffineHom B S hS _
    (inferInstanceAs (IsAffineHom ((affineOpenNhdsDiagram S s).map f)))

/-- The transition morphisms of the system of intersections of the affine open neighbourhoods
of `s` with `U` are affine: each is a base change of a transition morphism of the
neighbourhoods. -/
theorem isAffineHom_nbhdInterSystem (s : S) (U : S.Opens) {W W' : AffineOpenNhds S s}
    (f : W ⟶ W') : Space.IsAffineHom B S hS ((nbhdInterSystem B S hS s U ⋙ yoneda).map f) := by
  have h : W.obj.1 ≤ W'.obj.1 := leOfHom ((affineOpenNhds S s).ι.map f)
  have hpb := isPullback_homOfLE S (X := U ⊓ W'.obj.1) (Y := W.obj.1) (Z := W'.obj.1)
    (P := U ⊓ W.obj.1) (inf_le_inf_left U h) inf_le_right inf_le_right h
    (by rw [inf_assoc, inf_eq_right.2 h])
  exact isAffineHom_yoneda_map_of_isAffineHom B S hS _
    (MorphismProperty.of_isPullback (P := @AlgebraicGeometry.IsAffineHom.{u}) hpb.flip
      (inferInstanceAs (IsAffineHom ((affineOpenNhdsDiagram S s).map f))))

/-- Every affine open neighbourhood of `s` is quasi-compact. -/
theorem isQuasiCompactSpace_nbhdSystem (s : S) (W : AffineOpenNhds S s) :
    Space.IsQuasiCompactSpace B S hS ((nbhdSystem B S hS s ⋙ yoneda).obj W) :=
  Space.isQuasiCompactSpace_yoneda_of_compactSpace B S hS _
    (inferInstanceAs (CompactSpace ((affineOpenNhdsDiagram S s).obj W)))

/-- The intersection of an affine open neighbourhood of `s` with `U` is quasi-compact when the
inclusion `U ⟶ S` is. -/
theorem isQuasiCompactSpace_nbhdInterSystem (s : S) (U : S.Opens) (hqc : QuasiCompact U.ι)
    (W : AffineOpenNhds S s) :
    Space.IsQuasiCompactSpace B S hS ((nbhdInterSystem B S hS s U ⋙ yoneda).obj W) := by
  refine Space.isQuasiCompactSpace_yoneda_of_compactSpace B S hS _ ?_
  have h₁ : IsCompact (U.ι ⁻¹' (W.obj.1 : Set S)) :=
    hqc.isCompact_preimage _ W.obj.1.2 (IsAffineOpen.isCompact W.property)
  have h₂ : IsCompact ((U ⊓ W.obj.1 : S.Opens) : Set S) := by
    have := h₁.image U.ι.continuous
    rwa [Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι, Set.inter_comm] at this
  exact isCompact_iff_compactSpace.1 h₂

/-- Every affine open neighbourhood of `s` is quasi-separated. -/
theorem isAbsolutelyQuasiSeparated_nbhdSystem (s : S) (W : AffineOpenNhds S s) :
    Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal
      ((nbhdSystem B S hS s ⋙ yoneda).obj W) :=
  Space.isAbsolutelyQuasiSeparated_yoneda_obj B S hS B.contains_terminal _
    (inferInstanceAs (QuasiSeparatedSpace ((affineOpenNhdsDiagram S s).obj W)))

/-- The intersection of an affine open neighbourhood of `s` with `U` is quasi-separated, being
an open subscheme of an affine scheme. -/
theorem isAbsolutelyQuasiSeparated_nbhdInterSystem (s : S) (U : S.Opens)
    (W : AffineOpenNhds S s) :
    Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal
      ((nbhdInterSystem B S hS s U ⋙ yoneda).obj W) :=
  Space.isAbsolutelyQuasiSeparated_yoneda_obj B S hS B.contains_terminal _
    (@Topology.IsOpenEmbedding.quasiSeparatedSpace _ _ _ _ _
      (inferInstanceAs (QuasiSeparatedSpace ((affineOpenNhdsDiagram S s).obj W)))
      (S.homOfLE (inf_le_right : U ⊓ W.obj.1 ≤ W.obj.1)).isOpenEmbedding)

/-- A system of subterminal objects of the site has uniformly bounded base changes. -/
private theorem baseChangeSizeBounded_of_isSubterminal {I : Type u} [Category.{u} I]
    (D : I ⥤ BigFppfOver B S hS) (hD : ∀ i, IsSubterminal (D.obj i)) :
    Space.BaseChangeSizeBounded B S hS (D ⋙ yoneda) :=
  Space.baseChangeSizeBounded_of_mono B S hS _ fun f => by
    have : Mono (D.map f) := mono_of_isSubterminal (hD _) _
    exact Functor.map_mono yoneda (D.map f)

/-- **Stacks 07SK for the affine open neighbourhoods of `s`**: base change exhibits the algebraic
spaces of finite presentation over `Spec 𝒪_{S,s}` as the filtered `2`-colimit of those over the
neighbourhoods. -/
theorem isFinitePresentationColimit_localCone (s : S) :
    IsFinitePresentationColimit B S hS (nbhdSystem B S hS s) (localObj B S hS s)
      (localToNbhd B S hS s) (fun _ => isSubterminal_opensObj B S hS _ _ _) :=
  isFinitePresentationColimit_of_isLimit (isLimitOfPreserves yoneda (isLimitLocalCone B S hS s))
    B.contains_terminal (isAffineHom_nbhdSystem B S hS s) (isQuasiCompactSpace_nbhdSystem B S hS s)
    (isAbsolutelyQuasiSeparated_nbhdSystem B S hS s) (mk_affineOpenNhds_lt B S hS s)
    (Cardinal.one_lt_aleph0.trans B.aleph0_lt_cutoff) (mk_hom_affineOpenNhds_le S s)
    (baseChangeSizeBounded_of_isSubterminal B S hS _ fun _ => isSubterminal_opensObj B S hS _)

/-- **Stacks 07SK for the intersections of the affine open neighbourhoods of `s` with `U`**:
base change exhibits the algebraic spaces of finite presentation over the punctured local scheme
as the filtered `2`-colimit of those over the intersections, which are quasi-compact because
`U ⟶ S` is. -/
theorem isFinitePresentationColimit_puncturedCone {s : S} {F : Set S}
    (hF : ∀ x ∈ F, IsClosed {x}) (hsF : s ∈ F) (U : S.Opens) (hU : (U : Set S) = Fᶜ)
    (hqc : QuasiCompact U.ι) :
    IsFinitePresentationColimit B S hS (nbhdInterSystem B S hS s U) (puncturedObj B S hS s)
      (puncturedToNbhdInter B S hS hF hsF U hU) (fun _ => isSubterminal_opensObj B S hS _ _ _) :=
  isFinitePresentationColimit_of_isLimit
    (isLimitOfPreserves yoneda (isLimitPuncturedCone B S hS hF hsF U hU))
    B.contains_terminal (isAffineHom_nbhdInterSystem B S hS s U)
    (isQuasiCompactSpace_nbhdInterSystem B S hS s U hqc)
    (isAbsolutelyQuasiSeparated_nbhdInterSystem B S hS s U) (mk_affineOpenNhds_lt B S hS s)
    (Cardinal.one_lt_aleph0.trans B.aleph0_lt_cutoff) (mk_hom_affineOpenNhds_le S s)
    (baseChangeSizeBounded_of_isSubterminal B S hS _ fun _ => isSubterminal_opensObj B S hS _)

/-! ### Stacks 0E90 -/

/-- **Stacks 0E90.** Let `s` be a closed point of `S` whose open complement `U = S ∖ {s}` has
quasi-compact inclusion, and let `V = Spec 𝒪_{S,s} ∖ {s}`. The comparison functor
`FP_S ⥤ FP_U ×_{FP_V} FP_{Spec 𝒪_{S,s}}`, which takes an algebraic space of finite presentation
over `S` to its base changes to `U` and to `Spec 𝒪_{S,s}` together with the canonical
identification of their base changes to `V`, is an equivalence of categories.

The affine open neighbourhoods `W` of `s` have `Spec 𝒪_{S,s}` as their limit and the `W ∩ U` have
`V` as theirs; Stacks 07SK turns these into colimit statements for the categories of algebraic
spaces of finite presentation, and Stacks 0E8Z for the coverings `S = U ∪ W` combines them. -/
theorem isEquivalence_glueingFunctor_closedPoint {s : S} (hs : IsClosed ({s} : Set S))
    (U : S.Opens) (hU : (U : Set S) = {s}ᶜ) (hqc : QuasiCompact U.ι) :
    (glueingFunctor B S hS (isPullback_punctured B S hS (F := {s})
      (fun x hx => (Set.mem_singleton_iff.1 hx) ▸ hs) (Set.mem_singleton s) U
        hU).w).IsEquivalence := by
  have hF : ∀ x ∈ ({s} : Set S), IsClosed {x} := fun x hx => (Set.mem_singleton_iff.1 hx) ▸ hs
  exact isEquivalence_glueingFunctor_of_colimit B S hS (s := s)
    (isPullback_punctured B S hS hF (Set.mem_singleton s) U hU)
    (hsqW := fun W => isPullback_opensObj_inf B S hS U W.obj.1)
    (hpNU := fun _ => isSubterminal_opensObj B S hS _ _ _)
    (hpNW := fun _ => isSubterminal_opensObj B S hS _ _ _)
    (hiUn := fun _ => isSubterminal_opensObj B S hS _ _ _)
    (hiWn := fun _ => isSubterminal_opensObj B S hS _ _ _)
    (isFinitePresentationColimit_localCone B S hS s)
    (isFinitePresentationColimit_puncturedCone B S hS hF (Set.mem_singleton s) U hU hqc)
    (inferInstanceAs (IsOpenImmersion U.ι))
    (fun W => inferInstanceAs (IsOpenImmersion (Scheme.Opens.ι (X := S) W.obj.1)))
    ((Scheme.Opens.range_ι U).trans hU)
    (fun W => (Scheme.Opens.range_ι (X := S) W.obj.1).symm ▸ W.obj.2)

end AlgebraicGeometry.FinitePresentationSpacesOver

end
