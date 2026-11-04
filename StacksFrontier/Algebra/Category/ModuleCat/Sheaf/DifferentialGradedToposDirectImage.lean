module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedBimoduleStructures
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedClosedSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedModuleTransport
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorEncodings

/-!
# The direct image of a sheaf of differential graded modules along a morphism of ringed topoi

Let `f : X ⟶ Y` be a morphism of ringed topoi, let `B` be a sheaf of differential graded
`O_X`-algebras, let `A` be a sheaf of differential graded `O_Y`-algebras and let
`ψ : A ⟶ f_*B` be a **unital** homomorphism of sheaves of differential graded `O_Y`-algebras.
The direct image

`f_{*,ψ} : Mod^dg(B) ⥤ Mod^dg(A)`

is built here out of two existing constructions and nothing else: the degree-`n` object is
`G(B^n)` for `G` the direct image of sheaves of modules, the differential is `G(d)`, and the
action of `A` is the action of `f_*B` with scalars restricted along `ψ`,

`G(Q^n) ⊗ A^i --(id ⊗ ψ_i)--> G(Q^n) ⊗ G(B^i) --μ--> G(Q^n ⊗ B^i) --G(action)--> G(Q^{n+i})`.

That is `SheafOfModules.DifferentialGradedModule.transportFunctor` followed by
`SheafOfModules.DifferentialGradedModule.restrictScalars`. The transport asks only that `G` be
**additive and lax monoidal**, which is what the direct image of sheaves of modules is — it is a
right adjoint, and a right adjoint of a monoidal functor is lax monoidal.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.toposPushforwardAlgebra` is `f_*B` as a sheaf of
  differential graded `O_Y`-algebras, the transport of `B` along `G`.
* `SheafOfModules.DifferentialGradedModule.toposPushforward`: **the direct image
  `f_{*,ψ} : Mod^dg(B) ⥤ Mod^dg(A)`**.
* `SheafOfModules.DifferentialGradedModule.closedSectionToposPushforwardIso`: **the sheaf of
  closed degree-`i` sections of `f_{*,ψ}Q` is the direct image of the sheaf of closed degree-`i`
  sections of `Q`.**

## Main results

* `SheafOfModules.DifferentialGradedModule.toposPushforward_obj_complex_X` and
  `toposPushforward_map_f`: the degreewise formulas, so a consumer never unfolds the definition.
* `SheafOfModules.DifferentialGradedModule.closedSectionToposPushforwardIso_naturality`: **that
  identification is natural in `Q`.**

## Implementation notes

**What is assumed and what is proved.** The functor `G` of sheaves of modules, its additivity and
its lax monoidal structure, and the comparison `ν` identifying the underlying sheaf of sets of
`G M` with the direct image of the underlying sheaf of sets of `M`, are **parameters**. They are
data about *ordinary* sheaves of modules, and they are the only thing here that is not proved:
everything about differential graded modules below is constructed from them.

That split is deliberate. In this development the morphism of ringed topoi `f` supplies
`Stacks.Sheaves.RingedToposModules.pushforwardModules` and `pullbackModules` together with their
adjunction (Tags 03D6, 03D7), and the comparison `ν` as
`moduleSheaf_pushforwardModules`; what it does **not** supply is a monoidal structure on the
pullback, and hence none on the direct image. `Stacks.SheafOfModules.pullbackTensorIso` (Tag
03EL) is a *binary* natural isomorphism of bifunctors and carries no associativity or unitality
coherence — a binary tensor isomorphism alone is not a monoidal structure — and the one missing
coherence is named, and left unproved, as
`Stacks.Sheaves.DerivedPullback.PullbackToposRightUnitorCoherence`. Of the two factors of
`pullbackModules`, only the second, `extendScalarsFSharp`, is monoidal
(`Stacks.Sheaves.RingedToposModules.extendScalarsFSharpMonoidal`); the first, the inverse image
of sheaves of modules of Tag 03D2, is not treated anywhere.

So the exact remaining obligation, deliberately stated at *ordinary module level* and not inside
any differential graded or Tag 0FSG argument, is: **produce `G.LaxMonoidal` and `G.Additive` for
`G = pushforwardModules f`, by way of an oplax monoidal structure on `pullbackModules f` and
`CategoryTheory.Adjunction.rightAdjointLaxMonoidal`.** Both precedents for that move exist —
`Stacks.PushforwardGradedAlgebra.pushforwardFunctorLaxMonoidal` for a morphism of ringed spaces
and `Stacks.DifferentialGradedPullbackConstruction.pushforwardLaxMonoidal` for a continuous
functor of sites — and in each case they rest on a `Functor.Monoidal` structure on the pullback
which the ringed-topos case lacks. Nothing below weakens or hides that.

**No continuity, no smallness, no site functor.** `f` enters only as a `MorphismOfTopoi` between
the two categories of sheaves of sets, so there is no functor between the two underlying
categories to put a hypothesis on, no `Small` or `EssentiallySmall` anywhere, and the two sites'
universes are independent.

**The coefficient universe is common, and that is a real boundary.** The transport is typed
`SheafOfModules.{w} (toRingCat J O_X) ⥤ SheafOfModules.{w} (toRingCat K O_Y)`: one and the same
module universe `w` for the two ringed topoi, whereas
`Stacks.Sheaves.RingedToposModules.pushforwardModules` allows `w_X ≠ w_Y`. This file is stated at
the common-`w` boundary. That is not disguised as generality and no universe-lifting comparison
is claimed; the two *site* universes are and remain independent.

**The sheaf conditions are discharged, not carried.** The transport takes
`Presheaf.IsSheaf J (structureRingPresheaf O.obj)` on each side; those follow from the structure
sheaves being sheaves, by `Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf`,
so they appear in no statement below.

**Unit preservation is kept.** `SheafOfModules.DifferentialGradedAlgebra.Hom` deliberately permits
non-unital homomorphisms, while restriction of scalars needs the unit — the unit axiom for the
restricted action is exactly `ψ 1 = 1`. So `hψ : ψ.IsUnital` is an explicit argument throughout
and is never dropped. The source's datum is a unital `φ : f⁻¹A ⟶ B` over `f⁻¹O_Y`; passing
between that and `ψ : A ⟶ f_*B` is the ordinary monoidal adjunction after extension of scalars
to `f^*_{O}A`, and that passage is **not** proved here: it is a second boundary of the same kind
as the monoidal one, and `ψ` is taken as the datum.

## References

* [Stacks Project, Tag 0FRU](https://stacks.math.columbia.edu/tag/0FRU)
* [Stacks Project, Tag 0FRG](https://stacks.math.columbia.edu/tag/0FRG)
* [Stacks Project, Tag 0FRP](https://stacks.math.columbia.edu/tag/0FRP)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CategoryTheory.Sheaf
open Stacks.SheafOfModules.TensorSheafification

universe w v₁ u₁ v₂ u₂

namespace SheafOfModules.DifferentialGradedModule

section DirectImage

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Psharp : Sheaf K CommRingCat.{w}}
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify K AddCommGrpCat.{w}]

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

variable (G : SheafOfModules.{w} (toRingCat J Osharp) ⥤ SheafOfModules.{w} (toRingCat K Psharp))
  [G.LaxMonoidal] [G.Additive]

/-- **The direct image of a sheaf of differential graded algebras along `G`**, the transport of
`B` along the additive lax monoidal `G`. Its cochain complex is `G` applied degreewise. -/
noncomputable abbrev toposPushforwardAlgebra
    (B : DifferentialGradedAlgebra.{w, w} (toRingCat J Osharp)) :
    DifferentialGradedAlgebra.{w, w} (toRingCat K Psharp) :=
  DifferentialGradedAlgebra.transport G
    (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf Osharp)
    (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf Psharp) B

variable {B : DifferentialGradedAlgebra.{w, w} (toRingCat J Osharp)}
  {A : DifferentialGradedAlgebra.{w, w} (toRingCat K Psharp)}

/-- **The direct image `f_{*,ψ} : Mod^dg(B) ⥤ Mod^dg(A)` of right differential graded modules**:
the transport along `G` followed by restriction of scalars along the unital `ψ : A ⟶ f_*B`. -/
noncomputable def toposPushforward (ψ : A ⟶ toposPushforwardAlgebra G B)
    (hψ : ψ.IsUnital) :
    DifferentialGradedModule.{w, w, w} B ⥤ DifferentialGradedModule.{w, w, w} A :=
  transportFunctor G
      (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf Osharp)
      (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf Psharp) ⋙
    restrictScalars ψ hψ

/-- The degree-`n` object of the direct image is the direct image of the degree-`n` object. -/
@[simp]
theorem toposPushforward_obj_complex_X (ψ : A ⟶ toposPushforwardAlgebra G B) (hψ : ψ.IsUnital)
    (Q : DifferentialGradedModule.{w, w, w} B) (n : ℤ) :
    ((toposPushforward G ψ hψ).obj Q).complex.X n = G.obj (Q.complex.X n) :=
  rfl

/-- The differential of the direct image is the direct image of the differential. -/
@[simp]
theorem toposPushforward_obj_complex_d (ψ : A ⟶ toposPushforwardAlgebra G B) (hψ : ψ.IsUnital)
    (Q : DifferentialGradedModule.{w, w, w} B) (n m : ℤ) :
    ((toposPushforward G ψ hψ).obj Q).complex.d n m = G.map (Q.complex.d n m) :=
  rfl

/-- The direct image of a morphism is the degreewise direct image. -/
@[simp]
theorem toposPushforward_map_f (ψ : A ⟶ toposPushforwardAlgebra G B) (hψ : ψ.IsUnital)
    {Q Q' : DifferentialGradedModule.{w, w, w} B} (g : Q ⟶ Q') (n : ℤ) :
    ((toposPushforward G ψ hψ).map g).toHomologicalComplex.f n =
      G.map (g.toHomologicalComplex.f n) :=
  rfl

/-- The action of `A` on the direct image is the action of `f_*B` with scalars restricted along
`ψ`, on local sections. -/
theorem toposPushforward_mul_app (ψ : A ⟶ toposPushforwardAlgebra G B) (hψ : ψ.IsUnital)
    (Q : DifferentialGradedModule.{w, w, w} B) (n i : ℤ) (U : Dᵒᵖ)
    (x : (G.obj (Q.complex.X n)).val.obj U) (y : (A.complex.X i).val.obj U) :
    (((toposPushforward G ψ hψ).obj Q).mul n i).app U x y =
      ((transport G Q
            (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf Osharp)
            (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf
              Psharp)).mul n i).app U x
        ((ψ.toHomologicalComplex.f i).val.app U y) :=
  rfl

/-! ### The closed sections of the direct image -/

variable (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w)))

/-- The direct image of sheaves of sets is a right adjoint, so it preserves limits. -/
instance isRightAdjoint_toposPushforward : f.pushforward.IsRightAdjoint :=
  f.adj.isRightAdjoint

variable (ν : toSetSheaf (toRingCat J Osharp) ⋙ f.pushforward ≅
    G ⋙ toSetSheaf (toRingCat K Psharp))

/-- The comparison `ν` in degree `i`, at the spelling the closed-section transport takes: its
target is the degree-`i` object of the direct image rather than `G` of the degree-`i` object.
The two are equal on the nose; naming the comparison once keeps the spelling fixed. -/
noncomputable abbrev toposPushforwardPieceIso (ψ : A ⟶ toposPushforwardAlgebra G B)
    (hψ : ψ.IsUnital) (Q : DifferentialGradedModule.{w, w, w} B) (i : ℤ) :
    f.pushforward.obj ((toSetSheaf (toRingCat J Osharp)).obj (Q.complex.X i)) ≅
      (toSetSheaf (toRingCat K Psharp)).obj
        (((toposPushforward G ψ hψ).obj Q).complex.X i) :=
  ν.app (Q.complex.X i)

/-- The comparison is natural in the module, at that spelling. -/
theorem toposPushforwardPieceIso_naturality (ψ : A ⟶ toposPushforwardAlgebra G B)
    (hψ : ψ.IsUnital) {Q Q' : DifferentialGradedModule.{w, w, w} B} (g : Q ⟶ Q') (i : ℤ) :
    f.pushforward.map ((toSetSheaf (toRingCat J Osharp)).map (g.toHomologicalComplex.f i)) ≫
        (toposPushforwardPieceIso G f ν ψ hψ Q' i).hom =
      (toposPushforwardPieceIso G f ν ψ hψ Q i).hom ≫
        (toSetSheaf (toRingCat K Psharp)).map
          (((toposPushforward G ψ hψ).map g).toHomologicalComplex.f i) :=
  ν.hom.naturality (g.toHomologicalComplex.f i)

/-- The intertwining square for the differentials, which is the naturality of `ν` at the
differential of `Q`. -/
theorem toposPushforward_dSetMap_square (ψ : A ⟶ toposPushforwardAlgebra G B) (hψ : ψ.IsUnital)
    (Q : DifferentialGradedModule.{w, w, w} B) (i : ℤ) :
    f.pushforward.map (dSetMap Q i) ≫ (toposPushforwardPieceIso G f ν ψ hψ Q (i + 1)).hom =
      (toposPushforwardPieceIso G f ν ψ hψ Q i).hom ≫
        dSetMap ((toposPushforward G ψ hψ).obj Q) i :=
  ν.hom.naturality (Q.complex.d i (i + 1))

/-- The intertwining square for the zero morphisms, which is the naturality of `ν` at the zero
morphism together with additivity of `G`. -/
theorem toposPushforward_zeroSetMap_square (ψ : A ⟶ toposPushforwardAlgebra G B)
    (hψ : ψ.IsUnital) (Q : DifferentialGradedModule.{w, w, w} B) (i : ℤ) :
    f.pushforward.map (zeroSetMap Q i) ≫ (toposPushforwardPieceIso G f ν ψ hψ Q (i + 1)).hom =
      (toposPushforwardPieceIso G f ν ψ hψ Q i).hom ≫
        zeroSetMap ((toposPushforward G ψ hψ).obj Q) i := by
  refine (ν.hom.naturality (0 : Q.complex.X i ⟶ Q.complex.X (i + 1))).trans ?_
  refine congrArg (fun ϑ ↦ (toposPushforwardPieceIso G f ν ψ hψ Q i).hom ≫
    (toSetSheaf (toRingCat K Psharp)).map ϑ) ?_
  exact G.map_zero _ _

/-- **The sheaf of closed degree-`i` local sections of the direct image is the direct image of
the sheaf of closed degree-`i` local sections.** The differential of `f_{*,ψ}Q` is `G(d)` and
restriction of scalars does not change the complex, so this is the transport of the equalizer of
the differential against zero along `f_*`, which preserves it, being a right adjoint. -/
noncomputable def closedSectionToposPushforwardIso (ψ : A ⟶ toposPushforwardAlgebra G B)
    (hψ : ψ.IsUnital) (Q : DifferentialGradedModule.{w, w, w} B) (i : ℤ) :
    f.pushforward.obj (closedSectionSheaf Q i) ≅
      closedSectionSheaf ((toposPushforward G ψ hψ).obj Q) i :=
  closedSectionSheafTransportIso f.pushforward Q ((toposPushforward G ψ hψ).obj Q) i
    (toposPushforwardPieceIso G f ν ψ hψ Q i) (toposPushforwardPieceIso G f ν ψ hψ Q (i + 1))
    (toposPushforward_dSetMap_square G f ν ψ hψ Q i)
    (toposPushforward_zeroSetMap_square G f ν ψ hψ Q i)

/-- The comparison is the one compatible with the two inclusions of the closed sections. -/
theorem closedSectionToposPushforwardIso_hom_comp_ι (ψ : A ⟶ toposPushforwardAlgebra G B)
    (hψ : ψ.IsUnital) (Q : DifferentialGradedModule.{w, w, w} B) (i : ℤ) :
    (closedSectionToposPushforwardIso G f ν ψ hψ Q i).hom ≫
        closedSectionι ((toposPushforward G ψ hψ).obj Q) i =
      f.pushforward.map (closedSectionι Q i) ≫
        (toposPushforwardPieceIso G f ν ψ hψ Q i).hom :=
  closedSectionSheafTransportIso_hom_comp_ι f.pushforward Q _ i _ _ _ _

/-- **The identification of the closed sections of the direct image is natural in `Q`.** Both
sides are morphisms into an equation fibre, whose inclusion is a monomorphism, so the square is
checked after composing with that inclusion, where it is the naturality of `ν`. -/
theorem closedSectionToposPushforwardIso_naturality (ψ : A ⟶ toposPushforwardAlgebra G B)
    (hψ : ψ.IsUnital) {Q Q' : DifferentialGradedModule.{w, w, w} B} (g : Q ⟶ Q') (i : ℤ) :
    f.pushforward.map (closedSectionMap g i) ≫
        (closedSectionToposPushforwardIso G f ν ψ hψ Q' i).hom =
      (closedSectionToposPushforwardIso G f ν ψ hψ Q i).hom ≫
        closedSectionMap ((toposPushforward G ψ hψ).map g) i := by
  refine (cancel_mono (closedSectionι ((toposPushforward G ψ hψ).obj Q') i)).1 ?_
  have hL : f.pushforward.map (closedSectionMap g i) ≫
        (closedSectionToposPushforwardIso G f ν ψ hψ Q' i).hom ≫
          closedSectionι ((toposPushforward G ψ hψ).obj Q') i =
      f.pushforward.map (closedSectionι Q i) ≫
        f.pushforward.map
            ((toSetSheaf (toRingCat J Osharp)).map (g.toHomologicalComplex.f i)) ≫
          (toposPushforwardPieceIso G f ν ψ hψ Q' i).hom := by
    rw [closedSectionToposPushforwardIso_hom_comp_ι, ← Category.assoc, ← Functor.map_comp,
      closedSectionMap_comp_ι, Functor.map_comp, Category.assoc]
  have hR : ((closedSectionToposPushforwardIso G f ν ψ hψ Q i).hom ≫
        closedSectionMap ((toposPushforward G ψ hψ).map g) i) ≫
          closedSectionι ((toposPushforward G ψ hψ).obj Q') i =
      f.pushforward.map (closedSectionι Q i) ≫
        (toposPushforwardPieceIso G f ν ψ hψ Q i).hom ≫
          (toSetSheaf (toRingCat K Psharp)).map
            (((toposPushforward G ψ hψ).map g).toHomologicalComplex.f i) := by
    rw [Category.assoc, closedSectionMap_comp_ι, ← Category.assoc,
      closedSectionToposPushforwardIso_hom_comp_ι, Category.assoc]
  rw [Category.assoc, hL, hR]
  exact congrArg (fun ϑ ↦ f.pushforward.map (closedSectionι Q i) ≫ ϑ)
    (toposPushforwardPieceIso_naturality G f ν ψ hψ g i)

end DirectImage

end SheafOfModules.DifferentialGradedModule

end
