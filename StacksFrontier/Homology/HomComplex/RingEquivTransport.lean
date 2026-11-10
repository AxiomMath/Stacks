module

public import StacksFrontier.Homology.ExtendScalars.AlongARingIsomorphism
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.Homology.HomComplex.Basic
public import StacksFrontier.Homology.Tor.ChangeOfRingsSpectralSequence

/-!
# Transport along a ring isomorphism of the target

Let `ε : S ≃+* T` be an isomorphism of commutative rings. Restriction of scalars along `ε⁻¹`
relabels an `S`-module as a `T`-module, `StacksDraft.ScalarTransport.relabel`; it is an
equivalence of categories, and two things are transported along it here.

* *Termwise extension of scalars*: for a ring map `φ : B → S`, extension of scalars along the
  composite `ε ∘ φ : B → T` is extension of scalars along `φ` followed by the relabelling.  This
  is `StacksDraft.ScalarTransport.extendScalarsCompRelabelIso`, and
  `StacksDraft.ScalarTransport.extendScalarsCompRelabelComplexIso` is the same statement for the
  induced functors on cochain complexes.
* *The Hom complex*: relabelling the `S`-linear Hom complex of two complexes of `S`-modules gives
  the `T`-linear Hom complex of their relabellings,
  `StacksDraft.ScalarTransport.homComplexRelabelIso`.

The two combine into `StacksDraft.ScalarTransport.nonempty_extendScalars_iso_homComplexR_comp`:
a complex whose termwise extension of scalars along `φ` is the Hom complex of the termwise
extensions of two further complexes has the same property along `ε ∘ φ`.

## Main definitions

* `StacksDraft.ScalarTransport.relabel`: restriction of scalars along `ε⁻¹`.
* `StacksDraft.ScalarTransport.homComplexRCongr`: the Hom complex of complexes in an `R`-linear
  category is functorial in both arguments.

## Main results

* `StacksDraft.ScalarTransport.extendScalarsCompRelabelComplexIso`: the transport of termwise
  extension of scalars.
* `StacksDraft.ScalarTransport.homComplexRelabelIso`: the transport of the Hom complex.
* `StacksDraft.ScalarTransport.nonempty_extendScalars_iso_homComplexR_comp`: the two together.
* `StacksDraft.ScalarTransport.isZero_homology_extendScalars_comp_iff`: the cohomology of the
  termwise extension of scalars along `ε ∘ φ` vanishes exactly when that of the termwise extension
  along `φ` does.
-/

@[expose] public section

open CategoryTheory CochainComplex CochainComplex.HomComplex
open Stacks.HomComplex.TensorHomMap

universe u

namespace StacksDraft.ScalarTransport

noncomputable section

/-! ### The Hom complex is functorial in both arguments -/

section Congr

variable (R : Type*) [Ring R] {C : Type*} [Category C] [Preadditive C] [Linear R C]

/-- Precomposition and postcomposition on the Hom complex commute: both send a cochain `z` to
`g ∘ z ∘ h`. -/
@[reassoc]
theorem postcomp_precomp {L' L M M' : CochainComplex C ℤ} (g : L' ⟶ L) (h : M ⟶ M') :
    postcomp R L M M' h ≫ precomp R L' L M' g =
      precomp R L' L M g ≫ postcomp R L' M M' h := by
  refine HomologicalComplex.hom_ext _ _ fun n => ModuleCat.hom_ext <| LinearMap.ext fun z => ?_
  change (Cochain.ofHom g).comp (z.comp (Cochain.ofHom h) (add_zero n)) (zero_add n) =
    ((Cochain.ofHom g).comp z (zero_add n)).comp (Cochain.ofHom h) (add_zero n)
  exact (Cochain.comp_assoc (Cochain.ofHom g) z (Cochain.ofHom h) (zero_add n) (add_zero n)
    (by omega)).symm

/-- **The Hom complex is functorial in both arguments.**  Isomorphic arguments give isomorphic
Hom complexes, by pre- and postcomposition with the two isomorphisms. -/
def homComplexRCongr {L L' M M' : CochainComplex C ℤ} (α : L ≅ L') (β : M ≅ M') :
    CochainComplex.HomComplexR R L M ≅ CochainComplex.HomComplexR R L' M' where
  hom := precomp R L' L M α.inv ≫ postcomp R L' M M' β.hom
  inv := precomp R L L' M' α.hom ≫ postcomp R L M' M β.inv
  hom_inv_id := by
    simp only [Category.assoc, postcomp_precomp_assoc, ← postcomp_comp, ← precomp_comp,
      Iso.hom_inv_id, precomp_id, postcomp_id, Category.comp_id]
  inv_hom_id := by
    simp only [Category.assoc, postcomp_precomp_assoc, ← postcomp_comp, ← precomp_comp,
      Iso.inv_hom_id, precomp_id, postcomp_id, Category.comp_id]

end Congr

/-! ### Relabelling along a ring isomorphism -/

variable {S T : Type u} [CommRing S] [CommRing T] (ε : S ≃+* T)

/-- **Relabelling along a ring isomorphism**: restriction of scalars along `ε⁻¹` reads an
`S`-module as a `T`-module, `t` acting as `ε⁻¹ t` does.  It is an equivalence of categories. -/
abbrev relabel : ModuleCat.{u} S ⥤ ModuleCat.{u} T :=
  ModuleCat.restrictScalars.{u, u, u} ε.symm.toRingHom

/-- Relabelling on complexes, termwise. -/
abbrev relabelComplex :
    CochainComplex (ModuleCat.{u} S) ℤ ⥤ CochainComplex (ModuleCat.{u} T) ℤ :=
  (relabel ε).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Relabelling is `ε`-semilinear on morphisms: it does not change a map, so the `S`-multiple
`s • f` becomes the `T`-multiple by `ε s`. -/
theorem relabel_map_smul (s : S) {X Y : ModuleCat.{u} S} (f : X ⟶ Y) :
    (relabel ε).map (s • f) = ε s • (relabel ε).map f := by
  refine ModuleCat.hom_ext <| LinearMap.ext fun x => ?_
  change _ = ε.symm (ε s) • f.hom x
  rw [RingEquiv.symm_apply_apply]
  rfl

/-- **Transport of extension of scalars along a ring isomorphism of the target.**  For
`φ : B → S`, extension of scalars along `ε ∘ φ : B → T` is extension of scalars along `φ`
followed by the relabelling. -/
def extendScalarsCompRelabelIso {B : Type u} [CommRing B] (φ : B →+* S) :
    ModuleCat.extendScalars.{u, u, u} (ε.toRingHom.comp φ) ≅
      ModuleCat.extendScalars.{u, u, u} φ ⋙ relabel ε :=
  ModuleCat.extendScalarsComp φ ε.toRingHom ≪≫
    Functor.isoWhiskerLeft _ (ModuleCat.extendScalarsIsoRestrictScalarsSymm ε)

/-- `StacksDraft.ScalarTransport.extendScalarsCompRelabelIso` for the induced functors on cochain
complexes: termwise extension of scalars along `ε ∘ φ` is termwise extension of scalars along `φ`
followed by termwise relabelling. -/
def extendScalarsCompRelabelComplexIso {B : Type u} [CommRing B] (φ : B →+* S) :
    (ModuleCat.extendScalars.{u, u, u}
          (ε.toRingHom.comp φ)).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        relabelComplex ε :=
  (Functor.mapHomologicalComplexCompIso (extendScalarsCompRelabelIso ε φ).symm
    (ComplexShape.up ℤ)).symm

/-! ### The Hom complex along a ring isomorphism -/

variable (L M : CochainComplex (ModuleCat.{u} S) ℤ)

/-- Relabelling a cochain is `ε`-semilinear: the `S`-multiple `s • z` becomes the `T`-multiple
by `ε s`. -/
theorem cochainMap_smul {n : ℤ} (s : S) (z : Cochain L M n) :
    Cochain.map (s • z) (relabel ε) = ε s • Cochain.map z (relabel ε) := by
  refine Cochain.ext _ _ fun p q hpq => ?_
  rw [Cochain.map_v, Cochain.smul_v, relabel_map_smul ε, Cochain.smul_v, Cochain.map_v]

/-- The degree-`n` component of the Hom-complex transport: a degree-`n` cochain between two
complexes of `S`-modules is, as a family of maps, a degree-`n` cochain between their
relabellings, and the identification is `T`-linear. -/
def cochainRelabelEquiv (n : ℤ) :
    ((relabelComplex ε).obj (CochainComplex.HomComplexR S L M)).X n ≃ₗ[T]
      Cochain ((relabelComplex ε).obj L) ((relabelComplex ε).obj M) n where
  toFun z := Cochain.map z (relabel ε)
  map_add' z w := Cochain.map_add z w (relabel ε)
  map_smul' t z := by
    have h := cochainMap_smul ε L M (ε.symm t) z
    rw [RingEquiv.apply_symm_apply] at h
    exact h
  invFun w := Cochain.mk fun p q hpq => (relabel ε).preimage (w.v p q hpq)
  left_inv z := Cochain.ext _ _ fun _ _ _ => (relabel ε).preimage_map _
  right_inv w := Cochain.ext _ _ fun _ _ _ => (relabel ε).map_preimage _

/-- **Transport of the Hom complex along a ring isomorphism of the target.**  The relabelling of
the `S`-linear Hom complex `Hom^•_S(L, M)` is the `T`-linear Hom complex of the relabellings of
`L` and `M`; in degree `n` it is `StacksDraft.ScalarTransport.cochainRelabelEquiv`. -/
def homComplexRelabelIso :
    (relabelComplex ε).obj (CochainComplex.HomComplexR S L M) ≅
      CochainComplex.HomComplexR T ((relabelComplex ε).obj L) ((relabelComplex ε).obj M) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (cochainRelabelEquiv ε L M n).toModuleIso)
    (fun n m _ => by
      refine ModuleCat.hom_ext <| LinearMap.ext fun z => ?_
      exact δ_map n m z (relabel ε))

/-! ### The two transports together -/

/-- **A base-change clause moved along a ring isomorphism of the target.**  Let `φ : B → S` be a
ring map, let `ε : S ≃+* T` be a ring isomorphism, and let `E`, `P`, `F` be complexes of
`B`-modules.  If the termwise extension of scalars of `E` along `φ` is the `S`-linear Hom complex
of the termwise extensions of `P` and `F`, then the termwise extension of scalars of `E` along
`ε ∘ φ` is the `T`-linear Hom complex of the termwise extensions of `P` and `F` along `ε ∘ φ`. -/
theorem nonempty_extendScalars_iso_homComplexR_comp {B : Type u} [CommRing B] (φ : B →+* S)
    (E P F : CochainComplex (ModuleCat.{u} B) ℤ)
    (h : Nonempty
      (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj E ≅
        CochainComplex.HomComplexR S
          (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P)
          (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj F))) :
    Nonempty
      (((ModuleCat.extendScalars.{u, u, u} (ε.toRingHom.comp φ)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj E ≅
        CochainComplex.HomComplexR T
          (((ModuleCat.extendScalars.{u, u, u} (ε.toRingHom.comp φ)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P)
          (((ModuleCat.extendScalars.{u, u, u} (ε.toRingHom.comp φ)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj F)) := by
  obtain ⟨e⟩ := h
  let Θ := extendScalarsCompRelabelComplexIso ε φ
  exact ⟨Θ.app E ≪≫ (relabelComplex ε).mapIso e ≪≫ homComplexRelabelIso ε _ _ ≪≫
    homComplexRCongr T (Θ.app P).symm (Θ.app F).symm⟩

/-! ### Vanishing cohomology across the transport -/

/-- Relabelling does not change the underlying module, so it neither creates nor destroys a zero
object. -/
theorem isZero_relabel_iff (X : ModuleCat.{u} S) :
    Limits.IsZero ((relabel ε).obj X) ↔ Limits.IsZero X := by
  rw [ModuleCat.isZero_iff_subsingleton, ModuleCat.isZero_iff_subsingleton]
  exact Iff.rfl

/-- **A vanishing hypothesis moved along a ring isomorphism of the target.**  For `φ : B → S` and
`ε : S ≃+* T`, the degree-`j` cohomology of the termwise extension of scalars of `E` along
`ε ∘ φ : B → T` vanishes exactly when that of the termwise extension along `φ` does. -/
theorem isZero_homology_extendScalars_comp_iff {B : Type u} [CommRing B] (φ : B →+* S)
    (E : CochainComplex (ModuleCat.{u} B) ℤ) (j : ℤ) :
    Limits.IsZero ((((ModuleCat.extendScalars.{u, u, u} (ε.toRingHom.comp φ)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj E).homology j) ↔
      Limits.IsZero ((((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj E).homology j) := by
  refine Iso.isZero_iff ?_ |>.trans (isZero_relabel_iff ε _)
  exact HomologicalComplex.homologyMapIso ((extendScalarsCompRelabelComplexIso ε φ).app E) j ≪≫
    CochainComplex.Tor.ChangeOfRingsSpectralSequence.restrictHomologyIso.{u, u}
      ε.symm.toRingHom _ j

end

end StacksDraft.ScalarTransport

end
