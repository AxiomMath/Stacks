module

public import StacksFrontier.CategoryTheory.Sites.AbelianSectionsTransport
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.DerivedGlobalSectionsCohomology
public import StacksFrontier.Topology.Simplicial.AugmentationFibreCohomology
public import StacksFrontier.Topology.Simplicial.AugmentationHigherDirectImage
public import StacksFrontier.Topology.Simplicial.Morphisms

/-!
# The direct image over an open is the sections over the fibre

**Part (2) of the proof of [Stacks, Tag 0D84].** Let `X` be a simplicial topological space, let
`a : X ⟶ Y` be an augmentation and let `V` be an open of `Y`.  Then the sections over `V` of the
direct image `a_*F` of an abelian sheaf `F` on `X_Zar` are the global sections of the
restriction of `F` to the total site of the fibre `X ×_Y V`:

`(a_*F)(V) ≅ Γ((X ×_Y V)_Zar, F|)`,  naturally in `F`.

The comparison is built on underlying sets and then transported to abelian groups by
`CategoryTheory.liftNatIsoAb`, both functors being additive.  On sets it is a chain of four
bijections: the underlying sheaf of sets of `a_*F` is the geometric direct image of the
underlying sheaf of sets of `F` (`Stacks.Topos.AbelianPushforward.abelianPushforward_forgetIso`,
an equality); its sections over `V` are the morphisms from the sheaf represented by `V`, hence
by adjunction the morphisms from `a⁻¹(V)` into `F`; the inverse image `a⁻¹(V)` is the *support
presheaf* of the fibre, whose sections over `(n, U)` are the proofs of `U ⊆ a_n⁻¹(V)`, so
morphisms out of it are compatible families of sections of `F` over the fibre
(`CategoryTheory.supportedSectionsEquiv`); and such a family is a morphism out of the constant
sheaf on `ℤ`, which corepresents global sections.

## Main definitions

* `Stacks.Topology.Simplicial.fibreMeet`: the right adjoint of the comparison of total sites,
  intersection with the fibre.
* `Stacks.Topology.Simplicial.fibreSupport`: the inverse image along the augmentation of the
  sheaf represented by `V`.

## Main results

* `Stacks.Topology.Simplicial.fibreImageAdjunction`: the comparison of total sites is left
  adjoint to intersection with the fibre.
* `Stacks.Topology.Simplicial.augmentationOpenEquiv`: the sections of `a⁻¹(V)` over `(n, U)` are
  the proofs of `U ⊆ a_n⁻¹(V)`.
* `Stacks.Topology.Simplicial.fibreSectionsHomEquiv`: the set-level comparison.
* `Stacks.Topology.Simplicial.augmentationFibreSections_iso_fibreRestrictedSections`:
  **`(a_*F)(V) ≅ Γ((X ×_Y V)_Zar, F|)`, naturally in `F`** — part (2) of the source proof.

## Implementation notes

The support presheaf is identified through the degreewise description of the inverse image of
Stacks 09W4 (1): in degree `n` it is the inverse image along `a_n` of the sheaf represented by
`V`, which is the sheaf represented by `a_n⁻¹(V)` (`CategoryTheory.topPullbackYoneda`).  Its
values are subsingletons because the hom-sets of a lattice of opens are, which is what makes
`CategoryTheory.supportedSectionsEquiv` applicable; the counit of the adjunction at `(n, U)` is
invertible exactly when `U ⊆ a_n⁻¹(V)`, which is what a section of the support presheaf
provides.

## References

* [Stacks Project, Tag 0D84](https://stacks.math.columbia.edu/tag/0D84)
* [Stacks Project, Tag 09W4](https://stacks.math.columbia.edu/tag/09W4)
* [Stacks Project, Tag 06UN](https://stacks.math.columbia.edu/tag/06UN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.Topology.Simplicial

attribute [local instance] opens_subcanonical

variable (X : SimplicialObject TopCat.{u}) (Y : TopCat.{u})
  (a : X ⟶ (SimplicialObject.const TopCat).obj Y) (V : Opens Y)

/-! ### The adjoint of the comparison of total sites -/

/-- **Intersection with the fibre**, the right adjoint of the comparison of total sites: an
object `(n, U)` of `X_Zar` is sent to the open of `a_n⁻¹(V)` that `U` cuts out. -/
abbrev fibreMeet : SimplicialOpen X ⥤ SimplicialOpen (fibreSpace X Y a V) :=
  SimplicialOpen.pullback (fibreInclusion X Y a V)

/-- **The comparison of total sites is left adjoint to intersection with the fibre.** Both
hom-sets are the simplex maps carrying the source open into the target one, the containment
being the same condition read on points of `X_n` or of `a_n⁻¹(V)`. -/
def fibreImageAdjunction : fibreImage X Y a V ⊣ fibreMeet X Y a V :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun W U =>
        { toFun := fun g =>
            { base := g.base
              le := fun x hx =>
                SimplicialOpen.Hom.le g (Fibre.mem_imageOpens X Y a V hx) }
          invFun := fun g =>
            { base := g.base
              le := by
                rintro y ⟨x, hx, rfl⟩
                exact SimplicialOpen.Hom.le g hx }
          left_inv := fun _ => SimplicialOpen.Hom.ext _ _ rfl
          right_inv := fun _ => SimplicialOpen.Hom.ext _ _ rfl }
      homEquiv_naturality_left_symm := fun _ _ => SimplicialOpen.Hom.ext _ _ rfl
      homEquiv_naturality_right := fun _ _ => SimplicialOpen.Hom.ext _ _ rfl }

/-- The counit of `fibreImageAdjunction` at `U` lies over the identity simplex map of
`U.degree`. -/
@[simp]
theorem fibreImageAdjunction_counit_base (U : SimplicialOpen X) :
    ((fibreImageAdjunction X Y a V).counit.app U).base = 𝟙 U.degree := rfl

/-- The counit of the adjunction at an object lying over the fibre is invertible: the image of
the part of `U` inside the fibre is `U` itself. -/
theorem isIso_fibreImageAdjunction_counit {U : SimplicialOpen X}
    (h : U.toOpens ≤ fibreOpens X Y a V U.degree) :
    IsIso ((fibreImageAdjunction X Y a V).counit.app U) := by
  refine ⟨⟨{ base := 𝟙 U.degree
             le := by
               intro y hy
               change X.map (𝟙 U.degree) y ∈
                 Fibre.imageOpens X Y a V (Fibre.preimageOpens X Y a V U.toOpens)
               rwa [Fibre.imageOpens_preimageOpens X Y a V h,
                 ConcreteCategory.congr_hom (X.map_id U.degree) y] }, ?_, ?_⟩⟩ <;>
    exact SimplicialOpen.Hom.ext _ _ (Category.id_comp _)

/-! ### The support presheaf of the fibre -/

/-- **The inverse image along the augmentation of the sheaf represented by `V`.** Its sections
over an object `(n, U)` of `X_Zar` are the proofs that `U ⊆ a_n⁻¹(V)`. -/
noncomputable abbrev fibreSupport : Sheaf (SimplicialOpen.grothendieckTopology X) (Type u) :=
  (augmentationMorphism X Y a).inverseImage.obj
    ((Opens.grothendieckTopology Y).yoneda.obj V)

/-- **The sections of `a⁻¹(V)` over `(n, U)` are the containments `U ⊆ a_n⁻¹(V)`.** The inverse
image is computed degreewise by Stacks 09W4 (1), and the inverse image along `a_n` of the sheaf
represented by `V` is the sheaf represented by `a_n⁻¹(V)`. -/
noncomputable def augmentationOpenEquiv (W : SimplicialOpen X) :
    (fibreSupport X Y a V).obj.obj (op W) ≃
      (W.toOpens ⟶ fibreOpens X Y a V W.degree) := by
  let E := sheafEquivalenceSimplicialSheafSystem X (Type u)
  let P := fibreSupport X Y a V
  let e₁ := (E.underlyingPresheafIso.app P).symm.app (op W)
  let e₂ := ((E.componentIso W.degree).app (E.toEquivalence.functor.obj P)).app
    (op W.toOpens)
  let e₃ := ((TopCat.Sheaf.forget (Type u) (X.obj W.degree)).mapIso
    ((augmentationMorphism_inverseImage_component X Y a W.degree).app
      ((Opens.grothendieckTopology Y).yoneda.obj V))).app (op W.toOpens)
  let e₄ := ((TopCat.Sheaf.forget (Type u) (X.obj W.degree)).mapIso
    (topPullbackYoneda (a.app W.degree) V)).app (op W.toOpens)
  exact (e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄).toEquiv

/-- The support presheaf `fibreSupport` has at most one section over each object. -/
theorem subsingleton_fibreSupport (W : (SimplicialOpen X)ᵒᵖ) :
    Subsingleton ((fibreSupport X Y a V).obj.obj W) :=
  (augmentationOpenEquiv X Y a V W.unop).injective.subsingleton

/-- An object of `X_Zar` over which the support presheaf has a section lies over the fibre. -/
theorem le_fibreOpens_of_fibreSupport {W : SimplicialOpen X}
    (p : (fibreSupport X Y a V).obj.obj (op W)) :
    W.toOpens ≤ fibreOpens X Y a V W.degree :=
  leOfHom (augmentationOpenEquiv X Y a V W p)

/-- The support presheaf has a canonical section over every object in the image of the
comparison of total sites. -/
noncomputable def fibreSupportSection (W : SimplicialOpen (fibreSpace X Y a V)) :
    (fibreSupport X Y a V).obj.obj (op ((fibreImage X Y a V).obj W)) :=
  (augmentationOpenEquiv X Y a V _).symm
    (homOfLE (Fibre.imageOpens_le X Y a V W.toOpens))

/-! ### The set-level comparison -/

section Chain

variable {X Y a V}

/-- Step one: the underlying sheaf of sets of the direct image is the geometric direct image of
the underlying sheaf of sets. -/
noncomputable def chain₀ (F : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{u}) :
    ((augmentationPushforwardAb X Y a).obj F).obj.obj (op V) ≃
      ((augmentationMorphism X Y a).pushforward.obj
        ((sheafCompose (SimplicialOpen.grothendieckTopology X)
          (forget Ab.{u})).obj F)).obj.obj (op V) :=
  (((sheafToPresheaf (Opens.grothendieckTopology Y) (Type u)).mapIso
    ((Stacks.Topos.AbelianPushforward.abelianPushforward_forgetIso
      (SimplicialOpen.grothendieckTopology X)
      (augmentationMorphismOfTopoi X Y a)).app F)).app (op V)).toEquiv

/-- The bijection `chain₀` is natural in the abelian sheaf `F`. -/
theorem chain₀_naturality
    {F G : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{u}} (f : F ⟶ G)
    (x : ((augmentationPushforwardAb X Y a).obj F).obj.obj (op V)) :
    chain₀ (V := V) G (((augmentationPushforwardAb X Y a).map f).hom.app (op V) x) =
      (((augmentationMorphism X Y a).pushforward.map
        ((sheafCompose (SimplicialOpen.grothendieckTopology X)
          (forget Ab.{u})).map f)).hom.app (op V)) (chain₀ (V := V) F x) := by
  have hh := congrArg (fun t => t.hom.app (op V))
    ((Stacks.Topos.AbelianPushforward.abelianPushforward_forgetIso
      (SimplicialOpen.grothendieckTopology X)
      (augmentationMorphismOfTopoi X Y a)).hom.naturality f)
  exact ConcreteCategory.congr_hom hh x

/-- Step two: sections over `V` are morphisms from the sheaf represented by `V`, hence by
adjunction morphisms out of its inverse image. -/
noncomputable def chain₁ (F : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{u}) :
    ((augmentationMorphism X Y a).pushforward.obj
        ((sheafCompose (SimplicialOpen.grothendieckTopology X)
          (forget Ab.{u})).obj F)).obj.obj (op V) ≃
      (fibreSupport X Y a V ⟶
        (sheafCompose (SimplicialOpen.grothendieckTopology X) (forget Ab.{u})).obj F) :=
  ((Opens.grothendieckTopology Y).yonedaEquiv (X := V)
      (F := (augmentationMorphism X Y a).pushforward.obj
        ((sheafCompose (SimplicialOpen.grothendieckTopology X)
          (forget Ab.{u})).obj F))).symm.trans
    ((augmentationMorphism X Y a).adj.homEquiv
      ((Opens.grothendieckTopology Y).yoneda.obj V) _).symm

/-- The bijection `chain₁` is natural in the abelian sheaf `F`. -/
theorem chain₁_naturality
    {F G : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{u}} (f : F ⟶ G)
    (y : ((augmentationMorphism X Y a).pushforward.obj
      ((sheafCompose (SimplicialOpen.grothendieckTopology X)
        (forget Ab.{u})).obj F)).obj.obj (op V)) :
    chain₁ (V := V) G
        (((augmentationMorphism X Y a).pushforward.map
          ((sheafCompose (SimplicialOpen.grothendieckTopology X)
            (forget Ab.{u})).map f)).hom.app (op V) y) =
      chain₁ (V := V) F y ≫
        (sheafCompose (SimplicialOpen.grothendieckTopology X) (forget Ab.{u})).map f := by
  refine (congrArg (fun z => ((augmentationMorphism X Y a).adj.homEquiv
    ((Opens.grothendieckTopology Y).yoneda.obj V) _).symm z) ?_).trans
    ((augmentationMorphism X Y a).adj.homEquiv_naturality_right_symm _ _)
  exact ((Opens.grothendieckTopology Y).yonedaEquiv_symm_naturality_right V
    ((augmentationMorphism X Y a).pushforward.map
      ((sheafCompose (SimplicialOpen.grothendieckTopology X) (forget Ab.{u})).map f)) y).symm

/-- Step three: morphisms out of the support presheaf of the fibre are compatible families of
sections over the fibre. -/
noncomputable def chain₂ (F : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{u}) :
    (fibreSupport X Y a V ⟶
        (sheafCompose (SimplicialOpen.grothendieckTopology X) (forget Ab.{u})).obj F) ≃
      ((Functor.const (SimplicialOpen (fibreSpace X Y a V))ᵒᵖ).obj PUnit ⟶
        ((fibreRestrictionAb X Y a V).obj F).obj ⋙ forget Ab.{u}) :=
  Sheaf.homEquiv.trans
    (supportedSectionsEquiv (fibreImage X Y a V) (fibreMeet X Y a V)
      (fibreImageAdjunction X Y a V) (fibreSupport X Y a V).obj _
      (subsingleton_fibreSupport X Y a V) (fibreSupportSection X Y a V)
      (fun _ p => isIso_fibreImageAdjunction_counit X Y a V
        (le_fibreOpens_of_fibreSupport X Y a V p)))

/-- The bijection `chain₂` is natural in the abelian sheaf `F`. -/
theorem chain₂_naturality
    {F G : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{u}} (f : F ⟶ G)
    (t : fibreSupport X Y a V ⟶
      (sheafCompose (SimplicialOpen.grothendieckTopology X) (forget Ab.{u})).obj F) :
    chain₂ (V := V) G
        (t ≫ (sheafCompose (SimplicialOpen.grothendieckTopology X) (forget Ab.{u})).map f) =
      chain₂ (V := V) F t ≫ Functor.whiskerLeft (fibreImage X Y a V).op
        ((sheafCompose (SimplicialOpen.grothendieckTopology X) (forget Ab.{u})).map f).hom :=
  supportedSectionsEquiv_naturality (fibreImage X Y a V) (fibreMeet X Y a V)
    (fibreImageAdjunction X Y a V) (fibreSupport X Y a V).obj
    (subsingleton_fibreSupport X Y a V) (fibreSupportSection X Y a V)
    (fun _ p => isIso_fibreImageAdjunction_counit X Y a V
      (le_fibreOpens_of_fibreSupport X Y a V p)) t.hom
    ((sheafCompose (SimplicialOpen.grothendieckTopology X) (forget Ab.{u})).map f).hom

/-- Step four: a compatible family of sections over the fibre is a global section of the
restriction. -/
noncomputable def chain₃ (F : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{u}) :
    ((Functor.const (SimplicialOpen (fibreSpace X Y a V))ᵒᵖ).obj PUnit ⟶
        ((fibreRestrictionAb X Y a V).obj F).obj ⋙ forget Ab.{u}) ≃
      (Sheaf.Γ (SimplicialOpen.grothendieckTopology (fibreSpace X Y a V)) Ab.{u}).obj
        ((fibreRestrictionAb X Y a V).obj F) :=
  (constantZHomEquiv (((fibreRestrictionAb X Y a V).obj F).obj)).symm.trans
    ((Sheaf.ΓHomEquiv (J := SimplicialOpen.grothendieckTopology (fibreSpace X Y a V))
        (A := Ab.{u}) (X := AddCommGrpCat.of (ULift ℤ))
        (F := (fibreRestrictionAb X Y a V).obj F)).trans
      (AddCommGrpCat.uliftZMultiplesAddEquiv _).toEquiv)

/-- Restriction to the fibre on underlying presheaves of sets is restriction of the underlying
presheaf of sets. -/
theorem fibreRestriction_whisker_eq
    {F G : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{u}} (f : F ⟶ G) :
    Functor.whiskerLeft (fibreImage X Y a V).op
        ((sheafCompose (SimplicialOpen.grothendieckTopology X) (forget Ab.{u})).map f).hom =
      Functor.whiskerRight ((fibreRestrictionAb X Y a V).map f).hom (forget Ab.{u}) := by
  apply NatTrans.ext
  rfl

/-- The bijection `chain₃` is natural in the abelian sheaf `F`. -/
theorem chain₃_naturality
    {F G : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{u}} (f : F ⟶ G)
    (t : (Functor.const (SimplicialOpen (fibreSpace X Y a V))ᵒᵖ).obj PUnit ⟶
      ((fibreRestrictionAb X Y a V).obj F).obj ⋙ forget Ab.{u}) :
    chain₃ (V := V) G (t ≫ Functor.whiskerLeft (fibreImage X Y a V).op
        ((sheafCompose (SimplicialOpen.grothendieckTopology X) (forget Ab.{u})).map f).hom) =
      ((Sheaf.Γ (SimplicialOpen.grothendieckTopology (fibreSpace X Y a V)) Ab.{u}).map
        ((fibreRestrictionAb X Y a V).map f)) (chain₃ (V := V) F t) := by
  rw [fibreRestriction_whisker_eq]
  dsimp only [chain₃, Equiv.trans_apply]
  rw [constantZHomEquiv_symm_naturality t ((fibreRestrictionAb X Y a V).map f).hom,
    Sheaf.ΓHomEquiv_naturality_right]
  rfl

end Chain

/-- **The set-level form of part (2) of the proof of Stacks 0D84.** The sections over `V` of the
direct image of an abelian sheaf `F` on `X_Zar` are the morphisms from the constant sheaf on `ℤ`
on the total site of the fibre into the restriction of `F`. -/
noncomputable def fibreSectionsHomEquiv
    (F : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{u}) :
    ((augmentationPushforwardAb X Y a).obj F).obj.obj (op V) ≃
      (fibreRestrictedSections X Y a V).obj F :=
  (chain₀ F).trans ((chain₁ F).trans ((chain₂ F).trans (chain₃ F)))

/-- The set-level comparison is natural in the abelian sheaf. -/
theorem fibreSectionsHomEquiv_naturality
    {F G : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{u}} (f : F ⟶ G)
    (x : ((augmentationPushforwardAb X Y a).obj F).obj.obj (op V)) :
    fibreSectionsHomEquiv X Y a V G
        (((augmentationPushforwardAb X Y a).map f).hom.app (op V) x) =
      ((fibreRestrictedSections X Y a V).map f) (fibreSectionsHomEquiv X Y a V F x) := by
  change chain₃ G (chain₂ G (chain₁ G (chain₀ G
      (((augmentationPushforwardAb X Y a).map f).hom.app (op V) x)))) =
    ((fibreRestrictedSections X Y a V).map f) (chain₃ F (chain₂ F (chain₁ F (chain₀ F x))))
  rw [chain₀_naturality f x, chain₁_naturality f (chain₀ F x),
    chain₂_naturality f (chain₁ F (chain₀ F x))]
  exact chain₃_naturality f (chain₂ F (chain₁ F (chain₀ F x)))

/-- The set-level comparison, as a natural isomorphism of the underlying `Type`-valued
functors. -/
noncomputable def fibreSectionsForgetNatIso :
    augmentationFibreSections X Y a V ⋙ forget Ab.{u} ≅
      fibreRestrictedSections X Y a V ⋙ forget Ab.{u} :=
  NatIso.ofComponents (F := augmentationFibreSections X Y a V ⋙ forget Ab.{u})
    (G := fibreRestrictedSections X Y a V ⋙ forget Ab.{u})
    (fun F => (fibreSectionsHomEquiv X Y a V F).toIso)
    (fun {F G} f => by
      ext x
      exact fibreSectionsHomEquiv_naturality X Y a V f x)

/-- **Stacks 0D84, part (2) of the proof.** The sections over `V` of the direct image of an
abelian sheaf `F` on `X_Zar` along an augmentation are the global sections over the total site of
the fibre `X ×_Y V` of the restriction of `F`, naturally in `F`. -/
@[stacks 0D84 "part (2) of the proof: the direct image over V is the sections over the fibre"]
noncomputable def augmentationFibreSections_iso_fibreRestrictedSections :
    augmentationFibreSections X Y a V ≅ fibreRestrictedSections X Y a V :=
  liftNatIsoAb (fibreSectionsForgetNatIso X Y a V)

end Stacks.Topology.Simplicial

end
