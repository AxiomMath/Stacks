module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedToposBaseChangeExtension
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeDifferentialGradedModuleToposPullback

/-!
# The pullback of a differential graded module along a morphism of ringed topoi

Let `f : (Sh(C'), O') ⟶ (Sh(C), O)` be a morphism of ringed topoi and let `A` be a sheaf of
differential graded `O`-algebras. The pullback of sheaves of modules `f^*` is strong monoidal
(Tag 03EL with its coherences) and left adjoint to the direct image `f_*`, so it transports `A` to
a sheaf of differential graded `O'`-algebras `f^*A` and every right differential graded
`A`-module `P` to a right differential graded `f^*A`-module `f^*P`. The unit of the adjunction is
a unital homomorphism `η : A ⟶ f_*f^*A`, and `f^*P` is **the pullback of `P` along
`(f, f^*A, η)`**: it corepresents `Q ↦ Hom_A(P, f_{*,η}Q)`.

More generally, for a sheaf of differential graded `O'`-algebras `B` and a unital
`ψ : A ⟶ f_*B`, the extension of scalars `f^*P ⊗_{f^*A} B` along the adjoint transpose
`f^*A ⟶ B` of `ψ` is a pullback of `P` along `(f, B, ψ)` (`toposBaseChangeCorepresentableBy`). So
**every** right differential graded module has a pullback along every base change, as an object
corepresenting `Q ↦ Hom_A(P, f_{*,ψ}Q)` — the existential conjunct of condition (3) of Tag 0FSA is
satisfied by every module, and condition (3) is a statement about the flatness of that pullback.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.toposInverseImageModules`: the pullback of sheaves of
  modules along a morphism of ringed topoi, typed at the `toRingCat` spelling, with its monoidal
  structure and its adjunction `toposInverseImageAdjunction` to the direct image.
* `SheafOfModules.DifferentialGradedModule.toposPullbackAlgebra` and `toposPullbackModule`: `f^*A`
  and `f^*P`, and `toposPullbackUnit` the unit `η : A ⟶ f_*f^*A`.
* `SheafOfModules.DifferentialGradedModule.toposPullbackCorepresentableBy`: **`f^*P` is the
  pullback of `P` along `(f, f^*A, η)`.**
* `SheafOfModules.DifferentialGradedModule.toposBaseChangeCorepresentableBy`: **`f^*P ⊗_{f^*A} B`
  is the pullback of `P` along `(f, B, ψ)`.**

## Main results

* `SheafOfModules.DifferentialGradedModule.transportHomForward_eq_comp`: the adjoint transpose of
  a homomorphism `φ : f^*A ⟶ B` is the unit followed by `f_*φ`.
* `SheafOfModules.DifferentialGradedModule.exists_toposBaseChange`: every right differential
  graded module has a pullback along every base change.

## Implementation notes

The extension of scalars is the tensor product functor of
`SheafOfModules.RelativeTensor.tensorFunctorDataDgTensorRight`, which lives at the module universe
`max u v` of the site `C' : Type u` with `Category.{v} C'`; so the general base change is stated
for ringed topoi whose coefficient universe is that of the site, which is where sheaves of modules
on a small site live.

## References

* [Stacks Project, Tag 0FSA](https://stacks.math.columbia.edu/tag/0FSA)
* [Stacks Project, Tag 0FRU](https://stacks.math.columbia.edu/tag/0FRU)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public section

open CategoryTheory MonoidalCategory CategoryTheory.Sheaf
open Stacks.Sheaves.RingedToposModules

universe w v₁ u₁ v₂ u₂

namespace SheafOfModules.DifferentialGradedModule

section Universal

variable {Y : AlgebraicGeometry.RingedTopos.{v₂, u₂, w}}
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
  [Y.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w}]
  {X : AlgebraicGeometry.RingedTopos.{v₁, u₁, w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
  [X.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify X.J AddCommGrpCat.{w}]

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

variable (f : RingedToposHom X Y)

/-- **The pullback of sheaves of modules along a morphism of ringed topoi**, at the `toRingCat`
spelling of the two sheaves of rings; it is `Stacks.Sheaves.RingedToposModules.pullbackModules`. -/
noncomputable def toposInverseImageModules :
    SheafOfModules.{w} (toRingCat Y.J Y.O) ⥤ SheafOfModules.{w} (toRingCat X.J X.O) :=
  f.pullbackModules

/-- The pullback of sheaves of modules along a morphism of ringed topoi is additive. -/
instance toposInverseImageModules_additive : (toposInverseImageModules f).Additive :=
  (pullbackAdjPushforwardModules f).left_adjoint_additive

/-- The pullback of sheaves of modules is monoidal, by Tag 03EL with its three coherences. -/
@[instance_reducible]
noncomputable instance toposInverseImageModules_monoidal :
    (toposInverseImageModules f).Monoidal :=
  Stacks.SheafOfModules.RingedToposPullback.pullbackMonoidal f

/-- The adjunction `f^* ⊣ f_*` of Tag 03D7, at the `toRingCat` spelling. -/
noncomputable abbrev toposInverseImageAdjunction :
    toposInverseImageModules f ⊣ toposDirectImageModules f :=
  pullbackAdjPushforwardModules f

/-- The lax monoidal structure of the direct image is the one the adjunction induces from the
monoidal structure of the pullback, so the adjunction is monoidal. -/
instance toposInverseImageAdjunction_isMonoidal :
    (toposInverseImageAdjunction f).IsMonoidal :=
  (toposInverseImageAdjunction f).instIsMonoidal

variable (A : DifferentialGradedAlgebra.{w, w} (toRingCat Y.J Y.O))

/-- **The pullback `f^*A` of a sheaf of differential graded algebras**, the transport of `A` along
the monoidal pullback of sheaves of modules. -/
noncomputable abbrev toposPullbackAlgebra : DifferentialGradedAlgebra.{w, w} (toRingCat X.J X.O) :=
  DifferentialGradedAlgebra.transport (toposInverseImageModules f)
    (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf Y.O)
    (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf X.O) A

/-- **The unit `η : A ⟶ f_*f^*A`** of the adjunction, a homomorphism of sheaves of differential
graded algebras. -/
noncomputable abbrev toposPullbackUnit :
    A ⟶ toposPushforwardAlgebra (toposDirectImageModules f) (toposPullbackAlgebra f A) :=
  transportUnit (toposInverseImageAdjunction f)
    (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf X.O)
    (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf Y.O) A

/-- The unit `η : A ⟶ f_*f^*A` is unital. -/
theorem isUnital_toposPullbackUnit : (toposPullbackUnit f A).IsUnital :=
  isUnital_transportUnit _ _ _ A

variable {A}

/-- **The pullback `f^*P` of a right differential graded `A`-module**, a right differential graded
`f^*A`-module. -/
noncomputable abbrev toposPullbackModule (P : DifferentialGradedModule.{w, w, w} A) :
    DifferentialGradedModule.{w, w, w} (toposPullbackAlgebra f A) :=
  transport (toposInverseImageModules f) P
    (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf Y.O)
    (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf X.O)

/-- The complex of `f^*P` is the pullback of sheaves of modules applied degreewise to that of
`P`. -/
theorem toposPullbackModule_complex (P : DifferentialGradedModule.{w, w, w} A) :
    (toposPullbackModule f P).complex =
      ((toposInverseImageModules f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P.complex :=
  rfl

/-- **`f^*P` is the pullback of `P` along `(f, f^*A, η)`**: it corepresents
`Q ↦ Hom_A(P, f_{*,η}Q)`. -/
noncomputable def toposPullbackCorepresentableBy (P : DifferentialGradedModule.{w, w, w} A) :
    (toposPushforward (toposDirectImageModules f) (toposPullbackUnit f A)
        (isUnital_toposPullbackUnit f A) ⋙ coyoneda.obj (Opposite.op P)).CorepresentableBy
      (toposPullbackModule f P) :=
  transportCorepresentableBy (toposInverseImageAdjunction f) _ _ P

/-- **The adjoint transpose of a homomorphism `φ : f^*A ⟶ B` is the unit followed by `f_*φ`.** -/
theorem transportHomForward_eq_comp {B : DifferentialGradedAlgebra.{w, w} (toRingCat X.J X.O)}
    (φ : toposPullbackAlgebra f A ⟶ B) :
    DifferentialGradedAlgebra.transportHomForward (toposInverseImageAdjunction f)
        (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf X.O)
        (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf Y.O) φ =
      compPushforwardHom (toposDirectImageModules f) (toposPullbackUnit f A) φ := by
  refine DifferentialGradedAlgebra.Hom.ext fun n => ?_
  refine (DifferentialGradedAlgebra.transportHomForward_f _ _ _ φ n).trans ?_
  refine (Adjunction.homEquiv_unit _ _ _ _).trans ?_
  rw [DifferentialGradedAlgebra.comp_f, transportUnit_f, DifferentialGradedAlgebra.transportHom_f]
  rfl

end Universal

section TransposeUnital

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Psharp : Sheaf K CommRingCat.{w}}
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify K AddCommGrpCat.{w}]

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

variable {L : SheafOfModules.{w} (toRingCat K Psharp) ⥤ SheafOfModules.{w} (toRingCat J Osharp)}
  {G : SheafOfModules.{w} (toRingCat J Osharp) ⥤ SheafOfModules.{w} (toRingCat K Psharp)}
  (adj : L ⊣ G) [L.Monoidal] [G.LaxMonoidal] [adj.IsMonoidal] [L.Additive] [G.Additive]
  (hO : Presheaf.IsSheaf J
    (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf Osharp.obj))
  (hP : Presheaf.IsSheaf K
    (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf Psharp.obj))
  {A : DifferentialGradedAlgebra.{w, w} (toRingCat J Osharp)}
  {B : DifferentialGradedAlgebra.{w, w} (toRingCat K Psharp)}

/-- **A homomorphism `L(B) ⟶ A` whose adjoint transpose is unital is unital.** -/
theorem isUnital_of_isUnital_transportHomForward
    (φ : DifferentialGradedAlgebra.transport L hP hO B ⟶ A)
    (h : (DifferentialGradedAlgebra.transportHomForward adj hO hP φ).IsUnital) :
    φ.IsUnital := by
  have h' := DifferentialGradedAlgebra.Hom.oneHom_comp_of_isUnital _ h
  have eL : GradedAlgebra.oneHom (DifferentialGradedAlgebra.transport L hP hO B).toGradedAlgebra =
      Stacks.MonoidalGraded.mapOne L (GradedAlgebra.oneHom B.toGradedAlgebra) :=
    GradedAlgebra.oneHom_transport L B.toGradedAlgebra hP hO
  have eG : GradedAlgebra.oneHom (DifferentialGradedAlgebra.transport G hO hP A).toGradedAlgebra =
      Stacks.MonoidalGraded.mapOne G (GradedAlgebra.oneHom A.toGradedAlgebra) :=
    GradedAlgebra.oneHom_transport G A.toGradedAlgebra hO hP
  let oneA : 𝟙_ (SheafOfModules.{w} (toRingCat J Osharp)) ⟶ A.complex.X 0 :=
    GradedAlgebra.oneHom A.toGradedAlgebra
  let oneB : 𝟙_ (SheafOfModules.{w} (toRingCat K Psharp)) ⟶ B.complex.X 0 :=
    GradedAlgebra.oneHom B.toGradedAlgebra
  have e1 : oneB ≫ adj.homEquiv _ _ (φ.toHomologicalComplex.f 0) =
      adj.homEquiv _ _ (L.map oneB ≫ φ.toHomologicalComplex.f 0) :=
    (adj.homEquiv_naturality_left _ _).symm
  have e2 : Functor.LaxMonoidal.ε G ≫ G.map oneA =
      adj.homEquiv _ _ (Functor.OplaxMonoidal.η L ≫ oneA) := by
    rw [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_comp, ← Category.assoc,
      Adjunction.unit_app_unit_comp_map_η]
  have e3 : L.map oneB ≫ φ.toHomologicalComplex.f 0 = Functor.OplaxMonoidal.η L ≫ oneA :=
    (adj.homEquiv _ _).injective (e1.symm.trans (h'.trans (eG.trans e2)))
  apply DifferentialGradedAlgebra.Hom.isUnital_of_oneHom_comp
  rw [eL]
  show Functor.LaxMonoidal.ε L ≫ L.map oneB ≫ φ.toHomologicalComplex.f 0 = oneA
  rw [e3, Functor.Monoidal.ε_η_assoc]

end TransposeUnital

section BaseChange

variable {Y : AlgebraicGeometry.RingedTopos.{v₂, u₂, max u₁ v₁}}
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{max u₁ v₁} RingCat.{max u₁ v₁})]
  [Y.J.HasSheafCompose (CategoryTheory.forget RingCat.{max u₁ v₁})]
  [Y.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{max u₁ v₁})]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{max u₁ v₁}]
  [HasSheafify Y.J AddCommGrpCat.{max u₁ v₁}]
  {X : AlgebraicGeometry.RingedTopos.{v₁, u₁, max u₁ v₁}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{max u₁ v₁} RingCat.{max u₁ v₁})]
  [X.J.HasSheafCompose (CategoryTheory.forget RingCat.{max u₁ v₁})]
  [X.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{max u₁ v₁})]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u₁ v₁}]
  [HasSheafify X.J AddCommGrpCat.{max u₁ v₁}]

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

variable (f : RingedToposHom X Y)
  {A : DifferentialGradedAlgebra.{max u₁ v₁, max u₁ v₁} (toRingCat Y.J Y.O)}
  {B : DifferentialGradedAlgebra.{max u₁ v₁, max u₁ v₁} (toRingCat X.J X.O)}
  (ψ : A ⟶ toposPushforwardAlgebra (toposDirectImageModules f) B) (hψ : ψ.IsUnital)

/-- The adjoint transpose `f^*A ⟶ B` of `ψ : A ⟶ f_*B`. -/
noncomputable abbrev toposBaseChangeStructureMap : toposPullbackAlgebra f A ⟶ B :=
  DifferentialGradedAlgebra.transportHomBackward (toposInverseImageAdjunction f)
    (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf X.O)
    (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf Y.O) ψ

/-- The adjoint transpose of the adjoint transpose `f^*A ⟶ B` of `ψ` is `ψ`. -/
private theorem transportHomForward_toposBaseChangeStructureMap :
    DifferentialGradedAlgebra.transportHomForward (toposInverseImageAdjunction f)
        (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf X.O)
        (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf Y.O)
        (toposBaseChangeStructureMap f ψ) = ψ :=
  (DifferentialGradedAlgebra.transportHomEquiv (toposInverseImageAdjunction f) _ _ B
    A).apply_symm_apply ψ

/-- `ψ` is the unit followed by `f_*` of its adjoint transpose. -/
theorem compPushforwardHom_toposBaseChangeStructureMap :
    compPushforwardHom (toposDirectImageModules f) (toposPullbackUnit f A)
      (toposBaseChangeStructureMap f ψ) = ψ :=
  (transportHomForward_eq_comp f _).symm.trans
    (transportHomForward_toposBaseChangeStructureMap f ψ)

include hψ in
/-- The adjoint transpose of a unital `ψ` is unital. -/
theorem isUnital_toposBaseChangeStructureMap : (toposBaseChangeStructureMap f ψ).IsUnital := by
  refine isUnital_of_isUnital_transportHomForward (toposInverseImageAdjunction f) _ _ _ ?_
  rwa [transportHomForward_toposBaseChangeStructureMap]

/-- A corepresentation of the pullback along `ψ₁` is one along any `ψ₂` equal to it. -/
noncomputable def corepresentableByOfEq {P : DifferentialGradedModule.{max u₁ v₁, max u₁ v₁,
      max u₁ v₁} A}
    {T : DifferentialGradedModule.{max u₁ v₁, max u₁ v₁, max u₁ v₁} B}
    {ψ₁ ψ₂ : A ⟶ toposPushforwardAlgebra (toposDirectImageModules f) B} (h : ψ₁ = ψ₂)
    (h₁ : ψ₁.IsUnital) (h₂ : ψ₂.IsUnital)
    (e : (toposPushforward (toposDirectImageModules f) ψ₁ h₁ ⋙
      coyoneda.obj (Opposite.op P)).CorepresentableBy T) :
    (toposPushforward (toposDirectImageModules f) ψ₂ h₂ ⋙
      coyoneda.obj (Opposite.op P)).CorepresentableBy T := by
  subst h
  exact e

/-- **Every right differential graded module has a pullback along every base change**: the
extension of scalars `f^*P ⊗_{f^*A} B` along the adjoint transpose of `ψ` corepresents
`Q ↦ Hom_A(P, f_{*,ψ}Q)`. -/
noncomputable def toposBaseChangeCorepresentableBy
    (P : DifferentialGradedModule.{max u₁ v₁, max u₁ v₁, max u₁ v₁} A) :
    (toposPushforward (toposDirectImageModules f) ψ hψ ⋙
        coyoneda.obj (Opposite.op P)).CorepresentableBy
      ((RelativeTensor.tensorFunctorDataDgTensorRight
        ((toposBaseChangeStructureMap f ψ).toBimodule
          (isUnital_toposBaseChangeStructureMap f ψ hψ))).functor.obj (toposPullbackModule f P)) :=
  corepresentableByOfEq f (compPushforwardHom_toposBaseChangeStructureMap f ψ) _ hψ
    (corepresentableByExtension (toposDirectImageModules f) (toposPullbackUnit f A)
      (isUnital_toposPullbackUnit f A) (toposBaseChangeStructureMap f ψ)
      (isUnital_toposBaseChangeStructureMap f ψ hψ) P (toposPullbackCorepresentableBy f P) _)

/-- **Every right differential graded module has a pullback along every base change.** -/
theorem exists_toposBaseChange
    (P : DifferentialGradedModule.{max u₁ v₁, max u₁ v₁, max u₁ v₁} A) :
    ∃ T : DifferentialGradedModule.{max u₁ v₁, max u₁ v₁, max u₁ v₁} B,
      Nonempty ((toposPushforward (toposDirectImageModules f) ψ hψ ⋙
        coyoneda.obj (Opposite.op P)).CorepresentableBy T) :=
  ⟨_, ⟨toposBaseChangeCorepresentableBy f ψ hψ P⟩⟩

/-- **The pullbacks of a module along every base change are acyclic as soon as its pullback
`f^*P` along the universal base change is K-flat and acyclic.** -/
theorem acyclic_of_toposCorepresentableBy
    (P : DifferentialGradedModule.{max u₁ v₁, max u₁ v₁, max u₁ v₁} A)
    (hflat : RelativeTensor.IsKFlat (toposPullbackModule f P))
    (hac : (toposPullbackModule f P).complex.Acyclic)
    {T : DifferentialGradedModule.{max u₁ v₁, max u₁ v₁, max u₁ v₁} B}
    (eT : (toposPushforward (toposDirectImageModules f) ψ hψ ⋙
      coyoneda.obj (Opposite.op P)).CorepresentableBy T) :
    T.complex.Acyclic :=
  acyclic_of_corepresentableBy_comp (toposDirectImageModules f) (toposPullbackUnit f A)
    (isUnital_toposPullbackUnit f A) (toposBaseChangeStructureMap f ψ)
    (isUnital_toposBaseChangeStructureMap f ψ hψ) P (toposPullbackCorepresentableBy f P)
    hflat hac (corepresentableByOfEq f (compPushforwardHom_toposBaseChangeStructureMap f ψ).symm
      hψ _ eT)

variable {f} in
/-- **The pullback of a good module along the universal base change `(f, f^*A, η)` is
K-flat.** -/
theorem isKFlat_toposPullbackModule_of_isGoodToposBaseChange
    [HasSheafify Y.J (Type (max u₁ v₁))]
    {P : DifferentialGradedModule.{max u₁ v₁, max u₁ v₁, max u₁ v₁} A}
    (hP : IsGoodToposBaseChange.{max u₁ v₁, v₁, u₁} P) :
    RelativeTensor.IsKFlat (toposPullbackModule f P) :=
  ((hP.baseChange f (toposPullbackAlgebra f A) (toposPullbackUnit f A)
    (isUnital_toposPullbackUnit f A)).2 _ (toposPullbackCorepresentableBy f P)).2

end BaseChange

end SheafOfModules.DifferentialGradedModule

end
