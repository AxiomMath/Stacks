module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.Basic

/-!
# The direct-sum formula for extension by zero

Let `j : U ⟶ X` be an étale morphism of schemes.  Extension by zero `j_!` was built in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.Basic` as the sheafification of
the left Kan extension along composition with `j`.  This file computes that left Kan extension:
its sections over a scheme `V` étale over `X` are

```
(j_{p!} F)(V) = ⨁_{φ : V → U} F(V →^φ U)
```

the direct sum over the morphisms `φ : V ⟶ U` *over* `X`, of the sections of `F` over `V`
regarded as a scheme étale over `U` through `φ`.  This is Stacks Tag 0F4K.

The index set is realised as the set of morphisms `V ⟶ U` of the small étale site of `X`, where
`U` is viewed as a scheme étale over `X` through `j`
(`AlgebraicGeometry.Scheme.Etale.smallEtaleSource`), and the `φ`-th summand is the value of `F`
at `AlgebraicGeometry.Scheme.Etale.sourceDescend j φ`, the scheme `V` regarded as étale over `U`
through `φ`.

## Main definitions

* `AlgebraicGeometry.Scheme.Etale.smallEtaleSource`: `U` as an object of the small étale site of
  `X`.
* `AlgebraicGeometry.Scheme.Etale.sourceDescend`: `V →^φ U` as an object of the small étale site
  of `U`.
* `AlgebraicGeometry.Scheme.Etale.composeIndex`: the index `φ : V ⟶ U` attached to an object of
  the comma category computing the left Kan extension.
* `AlgebraicGeometry.Scheme.Etale.costructuredTerminal`: the terminal object of the connected
  component indexed by `φ`.
* `Stacks.EtaleCohomology.extensionByZeroPresheaf`: the presheaf `j_{p!} F`, that is the left Kan
  extension of `F` along composition with `j`.
* `Stacks.EtaleCohomology.extensionByZeroSummandInclusion`: the inclusion of the `φ`-th summand
  into `(j_{p!} F)(V)`.

## Main results

* `AlgebraicGeometry.Scheme.Etale.composeIndex_eq_of_hom`: the index is constant on connected
  components of the comma category.
* `Stacks.EtaleCohomology.isIso_sigmaDesc_extensionByZeroSummandInclusion` and
  `Stacks.EtaleCohomology.extensionByZeroPresheafSectionIso`: **Stacks Tag 0F4K**, the
  direct-sum formula `(j_{p!} F)(V) = ⨁_{φ : V → U} F(V →^φ U)`.
* `Stacks.EtaleCohomology.extensionByZero_obj_eq_sheafify`: `j_! F` is the sheafification of
  `j_{p!} F`, the second assertion of Stacks Tag 0F4K.
* `Stacks.EtaleCohomology.extensionByZeroSummandInclusion_naturality`: the formula is natural
  in `F`.

## Implementation notes

The comma category `CostructuredArrow (smallEtaleCompose j).op (op V)` indexing the Kan extension
colimit decomposes into connected components indexed by the morphisms `φ : V ⟶ U` over `X`: an
object is a scheme `W` étale over `U` together with a morphism `V ⟶ W` over `X`, and composing
that morphism with the structure morphism of `W` gives a morphism `V ⟶ U` over `X` which is
unchanged along morphisms of the comma category (`composeIndex_eq_of_hom`).  Each component has a
terminal object, namely `W = V` with the identity (`costructuredTerminal`), so the colimit is the
direct sum of the values at those terminal objects.

Mathlib's `Stacks.Sites.ExtensionByZero.isIso_lanSigmaDesc` is the same formula for the
localization `Over.forget U` of an abstract site, but it is stated for a category `C : Type u`
with `Category.{u} C` and for the functor `Over.forget U`, whereas the small étale site of a
scheme lives in `Type (u + 1)` with `Category.{u}` and the functor here is
`CategoryTheory.MorphismProperty.Over.map`.  Neither hypothesis is met, so the computation is
redone here from the colimit.

As throughout this development, `rw` and `simp` are mostly unusable on goals mentioning objects of
`AlgebraicGeometry.Scheme.Etale`, because the motives are ill-typed under the default
transparency settings; the proofs below are therefore written in term mode with explicit
`congrArg` motives.

## References

* [Stacks Project, Tag 0F4K](https://stacks.math.columbia.edu/tag/0F4K)
* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe w₂ w₁ u v

attribute [local instance] AlgebraicGeometry.Etale.isStableUnderComposition
attribute [local instance] AlgebraicGeometry.Etale.instIsMultiplicativeScheme

namespace AlgebraicGeometry.Scheme.Etale

variable {U X : Scheme.{u}} (j : U ⟶ X) [hj : Etale j]

/-- The source `U` of an étale morphism `j : U ⟶ X`, regarded as an object of the small étale
site of `X` through `j`.  The index set of the direct-sum formula of Stacks Tag 0F4K for the
sections over `V` is the set of morphisms `V ⟶ smallEtaleSource j` of the small étale site of
`X`, that is the set of morphisms `V ⟶ U` over `X`. -/
def smallEtaleSource : X.Etale :=
  MorphismProperty.Over.mk ⊤ j hj

/-- The underlying scheme of `smallEtaleSource j` is `U`. -/
@[simp]
theorem smallEtaleSource_left : (smallEtaleSource j).left = U := rfl

/-- The structure morphism of `smallEtaleSource j` is `j`. -/
@[simp]
theorem smallEtaleSource_hom : (smallEtaleSource j).hom = j := rfl

/-- A morphism `φ : V ⟶ smallEtaleSource j` of the small étale site of `X` has étale underlying
morphism of schemes `φ.left : V.left ⟶ U`: both `V` and `smallEtaleSource j` are étale over `X`.
This is Mathlib's instance for morphisms of `AlgebraicGeometry.Scheme.Etale`, named so that it can
be supplied explicitly where instance search cannot see through `smallEtaleSource`. -/
theorem etale_left_of_hom_smallEtaleSource {V : X.Etale} (φ : V ⟶ smallEtaleSource j) :
    Etale φ.left :=
  inferInstance

/-- The object `V →^φ U` of the small étale site of `U` attached to a morphism
`φ : V ⟶ smallEtaleSource j` over `X`: the underlying scheme is that of `V` and the structure
morphism to `U` is `φ.left`.  This is the object at which `F` is evaluated in the `φ`-th summand
of the formula of Stacks Tag 0F4K. -/
def sourceDescend {V : X.Etale} (φ : V ⟶ smallEtaleSource j) : U.Etale :=
  MorphismProperty.Over.mk ⊤ φ.left (etale_left_of_hom_smallEtaleSource j φ)

/-- The underlying scheme of `sourceDescend j φ` is that of `V`. -/
@[simp]
theorem sourceDescend_left {V : X.Etale} (φ : V ⟶ smallEtaleSource j) :
    (sourceDescend j φ).left = V.left :=
  rfl

/-- The structure morphism of `sourceDescend j φ` to `U` is `φ.left`. -/
@[simp]
theorem sourceDescend_hom {V : X.Etale} (φ : V ⟶ smallEtaleSource j) :
    (sourceDescend j φ).hom = φ.left :=
  rfl

/-- Composing with `j` sends `sourceDescend j φ` back to `V`: the underlying scheme is unchanged
and the structure morphism to `X` is `φ.left ≫ j = V.hom`. -/
def sourceDescendIso {V : X.Etale} (φ : V ⟶ smallEtaleSource j) :
    (smallEtaleCompose j).obj (sourceDescend j φ) ≅ V :=
  MorphismProperty.Over.isoMk (Iso.refl _)
    ((Category.id_comp V.hom).trans (MorphismProperty.Over.w φ).symm)

/-- The underlying morphism of schemes of `sourceDescendIso j φ` is the identity. -/
@[simp]
theorem sourceDescendIso_hom_left {V : X.Etale} (φ : V ⟶ smallEtaleSource j) :
    (sourceDescendIso j φ).hom.left = 𝟙 V.left :=
  rfl

/-- The underlying morphism of schemes of the inverse of `sourceDescendIso j φ` is the
identity. -/
@[simp]
theorem sourceDescendIso_inv_left {V : X.Etale} (φ : V ⟶ smallEtaleSource j) :
    (sourceDescendIso j φ).inv.left = 𝟙 V.left :=
  rfl

/-- Transporting `sourceDescend j φ` along an equality of indices does not move the underlying
scheme: the underlying morphism of schemes of the induced `eqToHom` is the identity. -/
theorem sourceDescend_eqToHom_left {V : X.Etale} {φ ψ : V ⟶ smallEtaleSource j} (h : φ = ψ) :
    (eqToHom (congrArg (sourceDescend j) h)).left = 𝟙 V.left := by
  subst h
  rfl

/-- The index attached to an object of the comma category
`CostructuredArrow (smallEtaleCompose j).op (op V)` computing the left Kan extension along
composition with `j`: an object consists of a scheme `W` étale over `U` together with a morphism
`V ⟶ W` over `X`, and the index is the composite `V ⟶ U` over `X`. -/
def composeIndex {V : X.Etale} (c : CostructuredArrow (smallEtaleCompose j).op (op V)) :
    V ⟶ smallEtaleSource j :=
  MorphismProperty.Over.homMk (c.hom.unop.left ≫ c.left.unop.hom)
    ((Category.assoc _ _ _).trans (MorphismProperty.Over.w c.hom.unop))

/-- The underlying morphism of schemes of `composeIndex j c`. -/
@[simp]
theorem composeIndex_left {V : X.Etale} (c : CostructuredArrow (smallEtaleCompose j).op (op V)) :
    (composeIndex j c).left = c.hom.unop.left ≫ c.left.unop.hom :=
  rfl

/-- The object of the small étale site of `U` attached to the index of `c` is the one obtained
from the structure morphism of `c` by `AlgebraicGeometry.Scheme.Etale.composeDescend`. -/
theorem sourceDescend_composeIndex {V : X.Etale}
    (c : CostructuredArrow (smallEtaleCompose j).op (op V)) :
    sourceDescend j (composeIndex j c) = composeDescend j c.hom.unop :=
  rfl

/-- The canonical morphism from the object of the small étale site of `U` attached to the index
of `c` to the object underlying `c`. -/
def composeIndexHom {V : X.Etale} (c : CostructuredArrow (smallEtaleCompose j).op (op V)) :
    sourceDescend j (composeIndex j c) ⟶ c.left.unop :=
  composeDescendHom j c.hom.unop

/-- The underlying morphism of schemes of `composeIndexHom j c`. -/
@[simp]
theorem composeIndexHom_left {V : X.Etale}
    (c : CostructuredArrow (smallEtaleCompose j).op (op V)) :
    (composeIndexHom j c).left = c.hom.unop.left :=
  rfl

/-- A morphism `f : c ⟶ c'` of the comma category
`CostructuredArrow (smallEtaleCompose j).op (op V)` factors the structure morphism of `c` through
that of `c'`. -/
theorem hom_unop_left_comp_left {V : X.Etale}
    {c c' : CostructuredArrow (smallEtaleCompose j).op (op V)} (f : c ⟶ c') :
    c'.hom.unop.left ≫ f.left.unop.left = c.hom.unop.left :=
  congrArg (fun k : V ⟶ (smallEtaleCompose j).obj c.left.unop => k.left)
    (congrArg (fun k => k.unop) (CostructuredArrow.w f))

/-- The index is constant on connected components of the comma category: a morphism of
`CostructuredArrow (smallEtaleCompose j).op (op V)` does not change the attached morphism
`V ⟶ U` over `X`.  This is what makes the comma category decompose as a disjoint union indexed by
the morphisms `V ⟶ U`. -/
theorem composeIndex_eq_of_hom {V : X.Etale}
    {c c' : CostructuredArrow (smallEtaleCompose j).op (op V)} (f : c ⟶ c') :
    composeIndex j c = composeIndex j c' :=
  MorphismProperty.Over.Hom.ext <|
    (congrArg (fun k => k ≫ c.left.unop.hom) (hom_unop_left_comp_left j f).symm).trans <|
      (Category.assoc _ _ _).trans <|
        congrArg (fun k => c'.hom.unop.left ≫ k) (MorphismProperty.Over.w f.left.unop)

/-- The canonical morphisms attached to the index are compatible with a morphism `f : c ⟶ c'` of
the comma category: transporting along `composeIndex_eq_of_hom` and composing with `f` recovers
the canonical morphism at `c`. -/
theorem eqToHom_comp_composeIndexHom_comp {V : X.Etale}
    {c c' : CostructuredArrow (smallEtaleCompose j).op (op V)} (f : c ⟶ c') :
    eqToHom (congrArg (sourceDescend j) (composeIndex_eq_of_hom j f)) ≫
        composeIndexHom j c' ≫ f.left.unop =
      composeIndexHom j c :=
  MorphismProperty.Over.Hom.ext <|
    (congrArg (fun k => k ≫ c'.hom.unop.left ≫ f.left.unop.left)
        (sourceDescend_eqToHom_left j (composeIndex_eq_of_hom j f))).trans <|
      (Category.id_comp _).trans (hom_unop_left_comp_left j f)

/-- The terminal object of the connected component of the comma category
`CostructuredArrow (smallEtaleCompose j).op (op V)` indexed by `φ : V ⟶ U`: the scheme `V`
regarded as étale over `U` through `φ`, with the canonical identification of its composite with
`j` back with `V`. -/
def costructuredTerminal {V : X.Etale} (φ : V ⟶ smallEtaleSource j) :
    CostructuredArrow (smallEtaleCompose j).op (op V) :=
  CostructuredArrow.mk (S := (smallEtaleCompose j).op) (T := op V)
    (Y := op (sourceDescend j φ)) (sourceDescendIso j φ).inv.op

/-- The index of `costructuredTerminal j φ` is `φ`. -/
@[simp]
theorem composeIndex_costructuredTerminal {V : X.Etale} (φ : V ⟶ smallEtaleSource j) :
    composeIndex j (costructuredTerminal j φ) = φ :=
  MorphismProperty.Over.Hom.ext (Category.id_comp φ.left)

/-- The canonical morphism from an object of the comma category to the terminal object of its
connected component. -/
def toCostructuredTerminal {V : X.Etale}
    (c : CostructuredArrow (smallEtaleCompose j).op (op V)) :
    c ⟶ costructuredTerminal j (composeIndex j c) :=
  CostructuredArrow.homMk (composeIndexHom j c).op
    (Quiver.Hom.unop_inj (MorphismProperty.Over.Hom.ext (Category.id_comp c.hom.unop.left).symm))

end AlgebraicGeometry.Scheme.Etale

namespace Stacks.EtaleCohomology

open AlgebraicGeometry.Scheme.Etale

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]
  {A : Type w₁} [Category.{w₂} A]
  [∀ F : (U.Etale)ᵒᵖ ⥤ A, (smallEtaleCompose j).op.HasPointwiseLeftKanExtension F]
  [HasCoproducts.{u} A]

/-- The presheaf `j_{p!} F` of Stacks Tag 0F4K: the left Kan extension of `F` along composition
with `j`.  Extension by zero `Stacks.EtaleCohomology.extensionByZero` is its sheafification. -/
abbrev extensionByZeroPresheaf (F : (U.Etale)ᵒᵖ ⥤ A) : (X.Etale)ᵒᵖ ⥤ A :=
  (smallEtaleCompose j).op.lan.obj F

omit [∀ F : (U.Etale)ᵒᵖ ⥤ A, (smallEtaleCompose j).op.HasPointwiseLeftKanExtension F]
  [HasCoproducts.{u} A] in
/-- The family of summands of the formula of Stacks Tag 0F4K: the `φ`-th summand of the sections
of `j_{p!} F` over `V` is the value of `F` at `V` regarded as étale over `U` through `φ`. -/
abbrev extensionByZeroSummandFamily (F : (U.Etale)ᵒᵖ ⥤ A) (V : X.Etale) :
    (V ⟶ smallEtaleSource j) → A :=
  fun φ => F.obj (op (sourceDescend j φ))

omit [∀ F : (U.Etale)ᵒᵖ ⥤ A, (smallEtaleCompose j).op.HasPointwiseLeftKanExtension F] in
/-- Transporting the `φ`-th summand along an equality of indices `φ = ψ` agrees with the inclusion
of the `ψ`-th summand. -/
theorem map_eqToHom_op_comp_sigma_ι (F : (U.Etale)ᵒᵖ ⥤ A) {V : X.Etale}
    {φ ψ : V ⟶ smallEtaleSource j} (h : φ = ψ) :
    F.map (eqToHom (congrArg (sourceDescend j) h)).op ≫
        Sigma.ι (extensionByZeroSummandFamily j F V) φ =
      Sigma.ι (extensionByZeroSummandFamily j F V) ψ := by
  subst h
  simp

/-- The inclusion of the summand indexed by `φ : V ⟶ U` into the sections of `j_{p!} F` over `V`:
the component of the Kan extension unit at `V →^φ U`, followed by the identification of the
composite of `V →^φ U` with `j` back with `V`. -/
def extensionByZeroSummandInclusion (F : (U.Etale)ᵒᵖ ⥤ A) {V : X.Etale}
    (φ : V ⟶ smallEtaleSource j) :
    F.obj (op (sourceDescend j φ)) ⟶ (extensionByZeroPresheaf j F).obj (op V) :=
  ((smallEtaleCompose j).op.lanUnit.app F).app (op (sourceDescend j φ)) ≫
    (extensionByZeroPresheaf j F).map (sourceDescendIso j φ).inv.op

/-- The cocone, on the diagram computing the left Kan extension of `F` at `V`, whose vertex is the
direct sum of the summands of the formula of Stacks Tag 0F4K: its component at an object `c` of
the comma category is the inclusion of the summand indexed by `c`, precomposed with the value of
`F` at the canonical morphism from that summand to the object underlying `c`. -/
def extensionByZeroCocone (F : (U.Etale)ᵒᵖ ⥤ A) (V : X.Etale) :
    Cocone (CostructuredArrow.proj (smallEtaleCompose j).op (op V) ⋙ F) :=
  let fam := extensionByZeroSummandFamily j F V
  Cocone.mk (∐ fam)
    { app := fun c => F.map (composeIndexHom j c).op ≫ Sigma.ι fam (composeIndex j c)
      naturality := by
        intro c c' f
        refine Eq.trans ?_ (Category.comp_id
          (F.map (composeIndexHom j c).op ≫ Sigma.ι fam (composeIndex j c))).symm
        change F.map f.left ≫ F.map (composeIndexHom j c').op ≫ Sigma.ι fam (composeIndex j c') =
          F.map (composeIndexHom j c).op ≫ Sigma.ι fam (composeIndex j c)
        have hix : composeIndex j c = composeIndex j c' := composeIndex_eq_of_hom j f
        have hobj : sourceDescend j (composeIndex j c) = sourceDescend j (composeIndex j c') :=
          congrArg (sourceDescend j) hix
        calc F.map f.left ≫ F.map (composeIndexHom j c').op ≫ Sigma.ι fam (composeIndex j c')
            = F.map f.left ≫ F.map (composeIndexHom j c').op ≫ F.map (eqToHom hobj).op ≫
                Sigma.ι fam (composeIndex j c) :=
              congrArg (fun k => F.map f.left ≫ F.map (composeIndexHom j c').op ≫ k)
                (map_eqToHom_op_comp_sigma_ι j F hix).symm
          _ = F.map (f.left ≫ (composeIndexHom j c').op ≫ (eqToHom hobj).op) ≫
                Sigma.ι fam (composeIndex j c) := by
              simp only [Functor.map_comp, Category.assoc]
          _ = F.map (composeIndexHom j c).op ≫ Sigma.ι fam (composeIndex j c) :=
              congrArg (fun k => F.map k ≫ Sigma.ι fam (composeIndex j c))
                (Quiver.Hom.unop_inj
                  ((Category.assoc _ _ _).trans (eqToHom_comp_composeIndexHom_comp j f))) }

omit [∀ F : (U.Etale)ᵒᵖ ⥤ A, (smallEtaleCompose j).op.HasPointwiseLeftKanExtension F] in
/-- The component of `extensionByZeroCocone` at the terminal object of the connected component
indexed by `φ` is the inclusion of the `φ`-th summand. -/
theorem extensionByZeroCocone_ι_costructuredTerminal (F : (U.Etale)ᵒᵖ ⥤ A) {V : X.Etale}
    (φ : V ⟶ smallEtaleSource j) :
    (extensionByZeroCocone j F V).ι.app (costructuredTerminal j φ) =
      Sigma.ι (extensionByZeroSummandFamily j F V) φ := by
  have hk : composeIndexHom j (costructuredTerminal j φ) =
      eqToHom (congrArg (sourceDescend j) (composeIndex_costructuredTerminal j φ)) :=
    MorphismProperty.Over.Hom.ext
      (sourceDescend_eqToHom_left j (composeIndex_costructuredTerminal j φ)).symm
  show F.map (composeIndexHom j (costructuredTerminal j φ)).op ≫
      Sigma.ι (extensionByZeroSummandFamily j F V)
        (composeIndex j (costructuredTerminal j φ)) = _
  exact (congrArg (fun k => F.map (Quiver.Hom.op k) ≫
      Sigma.ι (extensionByZeroSummandFamily j F V)
        (composeIndex j (costructuredTerminal j φ))) hk).trans
    (map_eqToHom_op_comp_sigma_ι j F (composeIndex_costructuredTerminal j φ))

/-- `extensionByZeroCocone` is a colimit cocone: the comma category computing the left Kan
extension decomposes into connected components indexed by the morphisms `φ : V ⟶ U` over `X`, and
`costructuredTerminal j φ` is a terminal object of the `φ`-th component. -/
def isColimitExtensionByZeroCocone (F : (U.Etale)ᵒᵖ ⥤ A) (V : X.Etale) :
    IsColimit (extensionByZeroCocone j F V) :=
  IsColimit.mk (fun s => Sigma.desc fun φ => s.ι.app (costructuredTerminal j φ))
    (by
      intro s c
      change (F.map (composeIndexHom j c).op ≫
          Sigma.ι (extensionByZeroSummandFamily j F V) (composeIndex j c)) ≫
        Sigma.desc (fun φ => s.ι.app (costructuredTerminal j φ)) = s.ι.app c
      exact ((Category.assoc _ _ _).trans
        (congrArg (fun k => F.map (composeIndexHom j c).op ≫ k)
          (Sigma.ι_desc _ (composeIndex j c)))).trans
            (s.w (toCostructuredTerminal j c)))
    (fun s m hm => Sigma.hom_ext _ _ fun φ =>
      ((congrArg (fun k => k ≫ m)
        (extensionByZeroCocone_ι_costructuredTerminal j F φ).symm).trans
          (hm (costructuredTerminal j φ))).trans
            (Sigma.ι_desc (fun ψ => s.ι.app (costructuredTerminal j ψ)) φ).symm)

/-- **Stacks Project, Tag 0F4K.** The sections of the presheaf `j_{p!} F` over a scheme `V` étale
over `X` are the direct sum, over the morphisms `φ : V ⟶ U` over `X`, of the sections of `F` over
`V` regarded as étale over `U` through `φ`; the comparison map is the one induced on each summand
by the Kan extension unit. -/
@[stacks 0F4K "the presheaf formula (j_{p!} F)(V) = ⨁_{φ : V → U} F(V →^φ U)"]
theorem isIso_sigmaDesc_extensionByZeroSummandInclusion (F : (U.Etale)ᵒᵖ ⥤ A) (V : X.Etale) :
    IsIso (Sigma.desc
      (f := fun φ : V ⟶ smallEtaleSource j => F.obj (op (sourceDescend j φ)))
      (P := (extensionByZeroPresheaf j F).obj (op V))
      (fun φ => extensionByZeroSummandInclusion j F φ)) := by
  let L := (smallEtaleCompose j).op
  let G := CostructuredArrow.proj L (op V) ⋙ F
  let e₁ : (∐ extensionByZeroSummandFamily j F V) ≅ colimit G :=
    (isColimitExtensionByZeroCocone j F V).coconePointUniqueUpToIso (colimit.isColimit G)
  let e₂ : (extensionByZeroPresheaf j F).obj (op V) ≅ colimit G :=
    Functor.leftKanExtensionObjIsoColimit L F (op V)
  have he : Sigma.desc
      (f := fun φ : V ⟶ smallEtaleSource j => F.obj (op (sourceDescend j φ)))
      (P := (extensionByZeroPresheaf j F).obj (op V))
      (fun φ => extensionByZeroSummandInclusion j F φ) = (e₁ ≪≫ e₂.symm).hom := by
    refine Sigma.hom_ext _ _ fun φ => ?_
    have hunit : extensionByZeroSummandInclusion j F φ ≫ e₂.hom =
        colimit.ι G (costructuredTerminal j φ) :=
      (Category.assoc _ _ _).trans
        (Functor.leftKanExtensionUnit_leftKanExtension_map_leftKanExtensionObjIsoColimit_hom
          L F (op V) (costructuredTerminal j φ))
    have hcolim : Sigma.ι (extensionByZeroSummandFamily j F V) φ ≫ e₁.hom =
        colimit.ι G (costructuredTerminal j φ) :=
      (congrArg (fun k => k ≫ e₁.hom)
          (extensionByZeroCocone_ι_costructuredTerminal j F φ).symm).trans
        (IsColimit.comp_coconePointUniqueUpToIso_hom (isColimitExtensionByZeroCocone j F V)
          (colimit.isColimit G) (costructuredTerminal j φ))
    exact (Sigma.ι_desc _ φ).trans <|
      ((Iso.eq_comp_inv e₂).2 hunit).trans <|
        congrArg (fun k => k ≫ e₂.inv) hcolim.symm |>.trans (Category.assoc _ _ _)
  exact he ▸ inferInstance

/-- **Stacks Project, Tag 0F4K.** The direct-sum formula for the sections of the presheaf
`j_{p!} F` over a scheme `V` étale over `X`, as an isomorphism. -/
@[stacks 0F4K "the presheaf formula (j_{p!} F)(V) = ⨁_{φ : V → U} F(V →^φ U)"]
def extensionByZeroPresheafSectionIso (F : (U.Etale)ᵒᵖ ⥤ A) (V : X.Etale) :
    (∐ fun φ : V ⟶ smallEtaleSource j => F.obj (op (sourceDescend j φ))) ≅
      (extensionByZeroPresheaf j F).obj (op V) :=
  haveI := isIso_sigmaDesc_extensionByZeroSummandInclusion j F V
  asIso (Sigma.desc
    (f := fun φ : V ⟶ smallEtaleSource j => F.obj (op (sourceDescend j φ)))
    (P := (extensionByZeroPresheaf j F).obj (op V))
    (fun φ => extensionByZeroSummandInclusion j F φ))

omit [HasCoproducts.{u} A] in
/-- The summand inclusions of the direct-sum formula are natural in the presheaf. -/
theorem extensionByZeroSummandInclusion_naturality {F F' : (U.Etale)ᵒᵖ ⥤ A} (α : F ⟶ F')
    {V : X.Etale} (φ : V ⟶ smallEtaleSource j) :
    extensionByZeroSummandInclusion j F φ ≫ ((smallEtaleCompose j).op.lan.map α).app (op V) =
      α.app (op (sourceDescend j φ)) ≫ extensionByZeroSummandInclusion j F' φ := by
  have hunit : ((smallEtaleCompose j).op.lanUnit.app F).app (op (sourceDescend j φ)) ≫
      ((smallEtaleCompose j).op.lan.map α).app
        ((smallEtaleCompose j).op.obj (op (sourceDescend j φ))) =
      α.app (op (sourceDescend j φ)) ≫
        ((smallEtaleCompose j).op.lanUnit.app F').app (op (sourceDescend j φ)) :=
    congrArg (fun β => β.app (op (sourceDescend j φ)))
      ((smallEtaleCompose j).op.lanUnit.naturality α).symm
  calc extensionByZeroSummandInclusion j F φ ≫ ((smallEtaleCompose j).op.lan.map α).app (op V)
      = ((smallEtaleCompose j).op.lanUnit.app F).app (op (sourceDescend j φ)) ≫
          ((smallEtaleCompose j).op.lan.map α).app
            ((smallEtaleCompose j).op.obj (op (sourceDescend j φ))) ≫
          (extensionByZeroPresheaf j F').map (sourceDescendIso j φ).inv.op :=
        (Category.assoc _ _ _).trans
          (congrArg (fun k => ((smallEtaleCompose j).op.lanUnit.app F).app
            (op (sourceDescend j φ)) ≫ k)
              (((smallEtaleCompose j).op.lan.map α).naturality (sourceDescendIso j φ).inv.op))
    _ = α.app (op (sourceDescend j φ)) ≫ extensionByZeroSummandInclusion j F' φ :=
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun k => k ≫ (extensionByZeroPresheaf j F').map
            (sourceDescendIso j φ).inv.op) hunit)).trans (Category.assoc _ _ _)

end Stacks.EtaleCohomology

namespace Stacks.EtaleCohomology

open AlgebraicGeometry.Scheme.Etale

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]

/-- **Stacks Project, Tag 0F4K.** Extension by zero of an abelian sheaf is the sheafification of
the presheaf `j_{p!} F` whose sections are given by the direct-sum formula. -/
@[stacks 0F4K "j_! F is the sheafification of j_{p!} F"]
theorem extensionByZero_obj_eq_sheafify
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
    (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    (extensionByZero.{u, v} j).obj F =
      (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj
        (extensionByZeroPresheaf j F.obj) :=
  rfl

end Stacks.EtaleCohomology

end
