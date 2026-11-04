module

public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentOverEquiv
public import StacksFrontier.AlgebraicGeometry.ReflexiveHull.LocalKernelPresentation
import StacksCore.Tactic.EgaSgaAttribute
/-!
# The sheaf Hom out of a module of finite presentation is quasi-coherent

Let `X` be a scheme, let `F` be an `𝒪_X`-module of finite presentation and let `H` be a
quasi-coherent `𝒪_X`-module.  Then the internal Hom `SheafHom_{𝒪_X}(F, H)` is quasi-coherent.

This is the last item of the list in the Stacks Project's section
[Functoriality for quasi-coherent modules](https://stacks.math.columbia.edu/tag/01LA), and the
proof is the one indicated there: the first assertion of
[Stacks, Tag 01CQ](https://stacks.math.columbia.edu/tag/01CQ) exhibits `SheafHom(F, H)` locally
as the kernel of a map between finite direct sums of copies of `H`, and a kernel of a morphism
of quasi-coherent modules is quasi-coherent, which is
[Stacks, Tag 01LB](https://stacks.math.columbia.edu/tag/01LB).

Neither local Noetherianity of `X` nor coherence of `F` is used: finite presentation of `F` and
quasi-coherence of `H` suffice, over an arbitrary scheme.

## Main definitions

* `sheafHomModules F H`: the internal Hom `SheafHom_{𝒪_X}(F, H)` of two `𝒪_X`-modules, with
  arbitrary target.  At `H = 𝒪_X` this is the dual
  `Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf`.
* `HasLocalKernelPresentationHom X`: the first assertion of Tag 01CQ over the scheme `X`, for an
  arbitrary target, as a predicate on `X`.
* `sheafHomOverIso` and `sheafHomOverIhomIso`: **the restriction of the sheaf Hom is the sheaf
  Hom of the restrictions**, the second form reading the right-hand side as the internal hom of
  the monoidal closed structure on `𝒪_U`-modules.

## Main results

* `hasLocalKernelPresentationHom`: **the first assertion of Tag 01CQ over a scheme, for an
  arbitrary target**: `SheafHom(F, H)` is, around every point, the kernel of a morphism between
  two finite direct sums of copies of `H`.
* `isQuasicoherent_sheafHomModules`: **`SheafHom_{𝒪_X}(F, H)` is quasi-coherent** when `F` is of
  finite presentation and `H` is quasi-coherent.
* `isQuasicoherent_dualSheaf`: the dual of a module of finite presentation is quasi-coherent.

## Implementation notes

The local kernel presentation is the one of
`Stacks.AlgebraicGeometry.ReflexiveModules.hasLocalKernelPresentationDual` with the target
`𝒪_X` replaced by an arbitrary `H`.  That generalization is formal: the first-variable
continuity lemmas it rests on — `ihomCokernelIsoKernel`, `ihomCoproductIsoProduct` and
`ihomUnitIso` — are stated for an arbitrary target on an arbitrary ringed site, and so
is Tag 0E8H's `internalHomOverIso`, which identifies `SheafHom(F, H)|_U` with the sheaf Hom
computed on the slice site over `U`.  The two spellings of the sheaf of rings of the slice,
`X.ringCatSheaf.over U` and `Stacks.SheafOfModules.Tensor.ringSheaf (X.sheaf.over U)`, are handled
exactly as
there: `sliceTarget` is an `abbrev` that keeps the term on one side of the unfolding while the
category stays on the other.

The passage from the local kernel presentation to quasi-coherence is where the two sites have
to be compared.  The presentation lives on the slice site, where no scheme is available and
hence no kernel-of-quasi-coherent statement is; quasi-coherence of `SheafHom(F, H)` is wanted on
`X` itself.  Both steps are supplied by `Stacks.Modules.isQuasicoherent_restrict_of_slice`,
which pushes the slice-site kernel forward along `AlgebraicGeometry.Scheme.Modules.overEquiv`
into the modules on the open subscheme `U`, and by `Stacks.Modules.isQuasicoherent_of_restrict`,
which is the locality of quasi-coherence on the base.

**Scope relative to Tag 01CQ.**  Tag 01CQ is stated over an arbitrary ringed space, and
`hasLocalKernelPresentationHom` is proved only over a scheme: the local presentation of `F` is
taken from `SheafOfModules.IsFinitePresentation.exists_quasicoherentData`, and the conclusion is
phrased with `AlgebraicGeometry.Scheme.Opens`.  Tag 01CQ's second assertion, for coherent
targets, is `Stacks.SheafOfModules.isCoherent_of_locallyKernelFiniteCoproduct`, over an arbitrary
site.  The quasi-coherence theorem formalizes an unlabelled item of the enumeration in Section
01LA, which is a section label, not a lemma.

## References

* [Stacks Project, Tag 01LA](https://stacks.math.columbia.edu/tag/01LA)
* [Stacks Project, Tag 01CQ](https://stacks.math.columbia.edu/tag/01CQ)
* [Stacks Project, Tag 01LB](https://stacks.math.columbia.edu/tag/01LB)
* [Stacks Project, Tag 0E8H](https://stacks.math.columbia.edu/tag/0E8H)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite TopologicalSpace
open AlgebraicGeometry Stacks.SheafOfModules.InternalHom
open Stacks.AlgebraicGeometry.ReflexiveModules (dualSheaf schemeRingedSite)

noncomputable section

universe u

namespace Stacks.AlgebraicGeometry.InternalHomModules

variable {X : Scheme.{u}}

/-- **The internal Hom `SheafHom_{𝒪_X}(F, H)` of two modules on a scheme.**  Its sections over
an open `U` are the morphisms `F|_U ⟶ H|_U` of `𝒪_U`-modules.

This is Tag 03EM's internal Hom presheaf, which that tag shows to be a sheaf whenever the
target is.  At `H = 𝒪_X` it is the dual
`Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf`. -/
@[ega "0 5.4.2", ega "IV 18.5.1"]
public def sheafHomModules (F H : X.Modules) : X.Modules where
  val := internalHom X.sheaf.obj F.val H.val
  isSheaf := internalHom_isSheaf X.sheaf.obj F.val H.val H.isSheaf

/-- The dual is the internal Hom into the structure sheaf. -/
public theorem dualSheaf_eq (F : X.Modules) :
    dualSheaf F = sheafHomModules F (SheafOfModules.unit X.ringCatSheaf) := rfl

/-- **The first assertion of Stacks, Tag 01CQ over a scheme, for an arbitrary target.**  For
every `𝒪_X`-module `F` of finite presentation, every `𝒪_X`-module `H` and every point of `X`
there is an open neighbourhood on which `SheafHom_{𝒪_X}(F, H)` is the kernel of a morphism
between two finite direct sums of copies of `H`.

The presentation is read on the slice site over the neighbourhood, which is where
`SheafOfModules.QuasicoherentData` puts it. -/
public def HasLocalKernelPresentationHom (X : Scheme.{u}) : Prop :=
  ∀ (F H : X.Modules), F.IsFinitePresentation → ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ m n : ℕ,
    ∃ f : (∐ fun _ : Fin m => H.over U) ⟶ (∐ fun _ : Fin n => H.over U),
      Nonempty ((sheafHomModules F H).over U ≅ kernel f)

/-- **The restriction of the sheaf Hom is the sheaf Hom of the restrictions**,
`SheafHom(F, H)|_U ≅ SheafHom_{𝒪_U}(F|_U, H|_U)`, where the right-hand side is the internal Hom
of Tag 03EM computed on the slice site over `U`.

This is Tag 0E8H, `internalHomOverIso`, lifted from presheaves of modules to sheaves of
modules along the fully faithful forgetful functor. -/
public def sheafHomOverIso (X : Scheme.{u}) (U : X.Opens) (F H : X.Modules) :
    (sheafHomModules F H).over U ≅
      (internalHomSecondFunctor ((Opens.grothendieckTopology ↥X).over U)
        (X.sheaf.over U) (F.over U)).obj (H.over U) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (internalHomOverIso (schemeRingedSite X) U F H)

section

attribute [local instance] _root_.SheafOfModules.monoidalCategory
  _root_.SheafOfModules.symmetricCategory SheafOfModules.monoidalClosed

/-- **The target of the sheaf Hom, restricted to the slice site over `U`**, spelled as the
restriction `H|_U` that `HasLocalKernelPresentationHom` states its direct sums in, but typed as
a module over the slice's own structure sheaf `𝒪_{X|_U}`, which is the spelling instance search
needs.  The two sheaves of rings are the same by definitional unfolding; an `abbrev` keeps the
term on the `HasLocalKernelPresentationHom` side of that unfolding while the category stays on
the other, so that no coproduct ever has to be compared across it. -/
public abbrev sliceTarget (X : Scheme.{u}) (U : X.Opens) (H : X.Modules) :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.sheaf.over U)) :=
  H.over U

/-- **The sheaf Hom into `H|_U` on the slice site over `U`**, read as the internal hom of the
monoidal closed structure on `𝒪_U`-modules.  An `abbrev` so that it unifies with the underlying
`MonoidalClosed.internalHom` without a transport. -/
public abbrev sliceHom (X : Scheme.{u}) (U : X.Opens) (H : X.Modules) :
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.sheaf.over U)))ᵒᵖ ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.sheaf.over U)) :=
  MonoidalClosed.internalHom.flip.obj (sliceTarget X U H)

/-- **The restriction of the sheaf Hom, as the internal hom of the monoidal closed
structure.**  This is `sheafHomOverIso` followed by the internal-Hom bridge
`ihomIsoInternalHom`, which is what makes the first-variable continuity lemmas
`ihomCokernelIsoKernel` and `ihomCoproductIsoProduct` apply to it. -/
public def sheafHomOverIhomIso (X : Scheme.{u}) (U : X.Opens) (F H : X.Modules) :
    (sheafHomModules F H).over U ≅ (sliceHom X U H).obj (op (F.over U)) :=
  sheafHomOverIso X U F H ≪≫
    (ihomIsoInternalHom (X.sheaf.over U) (F.over U) (sliceTarget X U H)).symm

/-- **The sheaf Hom out of a finite free module on the slice site is a finite direct sum of
copies of `H|_U`.**  The sheaf Hom out of a coproduct is the product of the sheaf Homs, each
sheaf Hom out of `𝒪_U` is `H|_U`, and a finite product is a finite direct sum. -/
@[ega "0 5.4.2" "Hom_{O}(O^n,G) ≅ G^n"]
public def sliceHomFreeIsoSigma (X : Scheme.{u}) (U : X.Opens) (H : X.Modules) {ι : Type u}
    {k : ℕ} (e : ι ≃ Fin k) :
    (sliceHom X U H).obj (op (SheafOfModules.free (R := X.ringCatSheaf.over U) ι)) ≅
      ∐ fun _ : Fin k => sliceTarget X U H :=
  ihomCoproductIsoProduct (X.sheaf.over U) (sliceTarget X U H)
      (fun _ : ι => SheafOfModules.unit (X.ringCatSheaf.over U)) ≪≫
    Pi.whiskerEquiv (g := fun _ : Fin k => sliceTarget X U H) e
      (fun _ => (ihomUnitIso (X.sheaf.over U) (sliceTarget X U H)).symm) ≪≫
    (biproduct.isoProduct _).symm ≪≫ biproduct.isoCoproduct _

/-- **The first assertion of Stacks, Tag 01CQ over a scheme, for an arbitrary target**: for `F`
of finite presentation and `H` arbitrary, `SheafHom_{𝒪_X}(F, H)` is, around every point, the
kernel of a morphism between two finite direct sums of copies of `H`.

Finite presentation supplies a cover on whose members `F` is the cokernel of a morphism between
two finite free modules, which is `SheafOfModules.Presentation.isColimit`; applying
`SheafHom(-, H|_U)` turns that cokernel into a kernel, by `ihomCokernelIsoKernel`, and the two
finite free modules into finite direct sums of copies of `H|_U`, by `sliceHomFreeIsoSigma`.

Tag 01CQ is stated over a ringed space, whereas this is proved over a scheme, and that tag has a
second assertion besides this one; see the module docstring. -/
public theorem hasLocalKernelPresentationHom (X : Scheme.{u}) :
    HasLocalKernelPresentationHom X := by
  intro F H hF x
  obtain ⟨q, hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData F
  obtain ⟨i, hxU⟩ := ((Opens.coversTop_iff _ q.X).1 q.coversTop).exists_mem x
  have hPfin : (q.presentation i).IsFinite := hq.isFinite_presentation i
  have : Finite (q.presentation i).generators.I :=
    SheafOfModules.GeneratingSections.IsFiniteType.finite
  have : Finite (q.presentation i).relations.I :=
    SheafOfModules.GeneratingSections.IsFiniteType.finite
  obtain ⟨n, ⟨eg⟩⟩ := Finite.exists_equiv_fin (q.presentation i).generators.I
  obtain ⟨m, ⟨er⟩⟩ := Finite.exists_equiv_fin (q.presentation i).relations.I
  have isoG := sliceHomFreeIsoSigma X (q.X i) H eg
  have isoR := sliceHomFreeIsoSigma X (q.X i) H er
  obtain ⟨dg, ⟨hker⟩⟩ :
      ∃ dg : (sliceHom X (q.X i) H).obj
            (op (SheafOfModules.free (R := X.ringCatSheaf.over (q.X i))
              (q.presentation i).generators.I)) ⟶
          (sliceHom X (q.X i) H).obj
            (op (SheafOfModules.free (R := X.ringCatSheaf.over (q.X i))
              (q.presentation i).relations.I)),
        Nonempty ((sheafHomModules F H).over (q.X i) ≅ kernel dg) :=
    ⟨_, ⟨sheafHomOverIhomIso X (q.X i) F H ≪≫
      ihomCokernelIsoKernel (X.sheaf.over (q.X i)) _ (q.presentation i).isColimit⟩⟩
  exact ⟨q.X i, hxU, n, m, isoG.inv ≫ dg ≫ isoR.hom,
    ⟨hker ≪≫ kernel.mapIso dg _ isoG isoR
      (Iso.hom_inv_id_assoc isoG (dg ≫ isoR.hom)).symm⟩⟩

end

/-- **The sheaf Hom out of a module of finite presentation into a quasi-coherent module is
quasi-coherent.**  This is the last item of the enumeration of Stacks, Section 01LA.

Around every point, `SheafHom_{𝒪_X}(F, H)` is the kernel of a morphism between finite direct
sums of copies of `H` on the slice site, by `hasLocalKernelPresentationHom`.  Pushing that
kernel forward to the open subscheme identifies the restriction of `SheafHom_{𝒪_X}(F, H)` with
a kernel of a morphism of quasi-coherent modules there, hence a quasi-coherent module; and
quasi-coherence is local on the base. -/
public theorem isQuasicoherent_sheafHomModules (F H : X.Modules)
    (hF : F.IsFinitePresentation) [H.IsQuasicoherent] :
    (sheafHomModules F H).IsQuasicoherent := by
  choose U hxU m n f e using hasLocalKernelPresentationHom X F H hF
  refine Stacks.Modules.isQuasicoherent_of_restrict _ U ?_ fun x => ?_
  · exact le_antisymm le_top fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxU x⟩
  · exact Stacks.Modules.isQuasicoherent_restrict_of_slice (U x) _ (e x).some
      (Stacks.Modules.isQuasicoherent_overEquiv_kernel (U x) (f x)
        (Stacks.Modules.isQuasicoherent_overEquiv_sigma (U x) H (m x))
        (Stacks.Modules.isQuasicoherent_overEquiv_sigma (U x) H (n x)))

/-- **The dual of a module of finite presentation on a scheme is quasi-coherent**, the case
`H = 𝒪_X` of `isQuasicoherent_sheafHomModules`. -/
public theorem isQuasicoherent_dualSheaf (F : X.Modules) (hF : F.IsFinitePresentation) :
    (dualSheaf F).IsQuasicoherent :=
  isQuasicoherent_sheafHomModules F (SheafOfModules.unit X.ringCatSheaf) hF

end Stacks.AlgebraicGeometry.InternalHomModules

end

end
